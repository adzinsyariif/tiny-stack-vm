// A tiny stack VM: an interpreter for make.fun's 40-opcode stack ISA (32-bit wrapping
// values, a 256-deep data stack, 64 return addresses, 256 words of memory, byte input and
// output, a 1,000,000-step and a 65,536-byte output limit, ten traps), plus the driver that
// answers a whole set of instances. Checks run in the ISA's order — step limit, pc in
// range, opcode known, immediate fits, stack depth — before an instruction may act.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// What each opcode takes from the data stack (POPS) and leaves on it (PUSHES), one character
// per opcode byte 0x00..0x53 read off the ISA's stack pictures; '-' marks unnamed bytes.
const POPS = '00011223--------222222212221222-222-------------01100-----------12--------------1101';
const PUSHES = '01102233--------111111111111111-111-------------00000-----------10--------------0010';
// The two-operand operations, indexed by opcode - 0x10; the NEG, NOT and 0x1f slots stay
// empty (the first two are dispatched directly, the third is not an opcode).
const BIN = [
  (a, b) => a + b, (a, b) => a - b, (a, b) => Math.imul(a, b),
  (a, b) => a / b, (a, b) => a % b, (a, b) => Math.floor((a >>> 0) / (b >>> 0)), (a, b) => (a >>> 0) % (b >>> 0),
  null,
  (a, b) => a & b, (a, b) => a | b, (a, b) => a ^ b, null,
  (a, b) => a << (b & 31), (a, b) => a >> (b & 31), (a, b) => a >>> (b & 31), null,
  (a, b) => (a === b ? 1 : 0), (a, b) => (a < b ? 1 : 0), (a, b) => ((a >>> 0) < (b >>> 0) ? 1 : 0),
];

// Runs one program to its end: the bytes it wrote and the code it finished with.
function execute(code, input) {
  const stack = new Int32Array(256);
  const calls = new Int32Array(64);
  const mem = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, csp = 0, pc = 0, used = 0, olen = 0, ipos = 0;
  const n = code.length;
  const finish = (exitCode) => ({ bytes: out.slice(0, olen), code: exitCode });

  for (;;) {
    if (used === 1_000_000) return finish(10);
    if (pc < 0 || pc >= n) return finish(9);
    const op = code[pc];
    // The immediate's length follows from the opcode's family.
    const imm = op === 1 ? 1 : op === 2 ? 4 : op >= 0x30 && op <= 0x33 ? 2 : 0;
    if (imm > 0 && pc + imm >= n) return finish(9);
    const pk = POPS[op];
    if (pk === undefined || pk === '-') return finish(5);
    used++;
    if (sp < +pk) return finish(2);
    if (sp - +pk + +PUSHES[op] > 256) return finish(3);
    const next = pc + 1 + imm;
    pc = next;

    switch (op) {
      case 0x00: return finish(0); // HALT
      case 0x01: stack[sp++] = (code[next - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 0x02: // PUSH32, little-endian
        stack[sp++] = code[next - 4] | (code[next - 3] << 8) | (code[next - 2] << 16) | (code[next - 1] << 24);
        break;
      case 0x03: sp--; break;
      case 0x04: stack[sp] = stack[sp - 1]; sp++; break;
      case 0x05: {
        const t = stack[sp - 1];
        stack[sp - 1] = stack[sp - 2];
        stack[sp - 2] = t;
        break;
      }
      case 0x06: stack[sp] = stack[sp - 2]; sp++; break;
      case 0x07: { // ROT: ( a b c -- b c a )
        const a = stack[sp - 3];
        stack[sp - 3] = stack[sp - 2];
        stack[sp - 2] = stack[sp - 1];
        stack[sp - 1] = a;
        break;
      }
      case 0x17: stack[sp - 1] = -stack[sp - 1]; break;
      case 0x1b: stack[sp - 1] = ~stack[sp - 1]; break;
      case 0x30:
      case 0x31:
      case 0x32: { // JMP / JZ / JNZ: target is next + the signed offset, unchecked until used
        const rel = ((code[next - 2] | (code[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          const v = stack[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = next + rel;
        break;
      }
      case 0x33: // CALL: the immediate is an unsigned absolute address
        if (csp === 64) return finish(7);
        calls[csp++] = next;
        pc = code[next - 2] | (code[next - 1] << 8);
        break;
      case 0x34:
        if (csp === 0) return finish(8);
        pc = calls[--csp];
        break;
      case 0x40: {
        const addr = stack[sp - 1];
        if (addr < 0 || addr > 255) return finish(6);
        stack[sp - 1] = mem[addr];
        break;
      }
      case 0x41: { // STORE: ( v addr -- )
        const addr = stack[sp - 1];
        if (addr < 0 || addr > 255) return finish(6);
        mem[addr] = stack[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: { // PRINT: decimal; the whole write is refused past the output cap
        const text = String(stack[sp - 1]);
        if (olen + text.length > 65536) return finish(11);
        for (let i = 0; i < text.length; i++) out[olen++] = text.charCodeAt(i);
        sp--;
        break;
      }
      case 0x51:
        if (olen + 1 > 65536) return finish(11);
        out[olen++] = stack[--sp] & 255;
        break;
      case 0x52: // IN: -1 once the input is used up
        stack[sp++] = ipos < input.length ? input[ipos++] : -1;
        break;
      case 0x53: return finish(stack[sp - 1] & 255);
      default: { // the two-operand group; 0x13..0x16 trap 4 on a zero divisor first
        const b = stack[sp - 1];
        if (op >= 0x13 && op <= 0x16 && b === 0) return finish(4);
        stack[sp - 2] = BIN[op - 0x10](stack[sp - 2], b);
        sp--;
        break;
      }
    }
  }
}

const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(IN_DIR).sort()) {
  if (!/^i\d{3}$/.test(id)) continue;
  const dir = join(IN_DIR, id);
  const prog = new Uint8Array(readFileSync(join(dir, 'program.bin')));
  const inp = new Uint8Array(readFileSync(join(dir, 'input.bin')));
  const { bytes, code } = execute(prog, inp);
  mkdirSync(join(OUT_DIR, id), { recursive: true });
  writeFileSync(join(OUT_DIR, id, 'stdout.bin'), bytes);
  writeFileSync(join(OUT_DIR, id, 'exit.txt'), `${code}\n`);
}
