-- Prove2me | Theorems.Thm_IntMul_GrowingCounter_increment_counter
-- name    : IntMul.GrowingCounter.increment_counter
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T14:23:38.861298+00:00
-- url     : https://prove2.me/theorems/733788b2-7a40-4241-a5e8-2b865b173f7d
-- title:
--   Complete physical unbounded binary increment with exact clock and amortized linear bound
-- statement:
--   Let $b$ be any finite little-endian binary counter word, including the empty zero word. Let $r(b)$ be its number of initial one bits and $\Phi(b)$ its total number of one bits. A fixed three-tape machine physically increments the word, extending its tape representation into the actual blank if necessary, seeks its real start marker and returns to its first payload cursor after exactly
--
--   $$C(b)=2r(b)+2$$
--
--   actual transitions. It reaches the exact terminal caller frame, globally halts, retains both input and output caller tapes and heads, increases the binary value by one, and grows the counter width by at most one. Its potential identity is
--
--   $$C(b)+2\Phi(b+1)=4+2\Phi(b).$$
--
--   Consequently the sum of the proved physical per-call costs for $n$ increments is at most $4n+2\Phi(b)$, and the resulting counter value is its initial value plus $n$. In particular increments starting from the empty zero representation have total cost at most $4n$. Restart dispatch costs of a surrounding reader remain separate.
-- source:
--   Original complete actual growing binary counter for input-derived descriptors. Owns every bit write, blank extension, real marker rewind, terminal frame, value proof and amortized cost identity. Written by Codex.

import Definitions.Def_IntMul_GrowingCounter
import Mathlib.Tactic

open IntMul IntMul.GrowingCounter

theorem IntMul.GrowingCounter.increment_counter (base : machine.Cfg) (bits : List Bool) :
    machine.step^[counterSteps bits] (counterFrame base .carry bits)=counterFrame base .halt (increment bits) ∧
      (machine.step^[counterSteps bits] (counterFrame base .carry bits)).state=machine.qHalt ∧
      (machine.step^[counterSteps bits] (counterFrame base .carry bits)).cells 0=base.cells 0 ∧
      (machine.step^[counterSteps bits] (counterFrame base .carry bits)).head 0=base.head 0 ∧
      (machine.step^[counterSteps bits] (counterFrame base .carry bits)).cells 1=base.cells 1 ∧
      (machine.step^[counterSteps bits] (counterFrame base .carry bits)).head 1=base.head 1 ∧
      BinaryAdder.littleVal (increment bits)=BinaryAdder.littleVal bits+1 ∧
      (increment bits).length ≤ bits.length+1 ∧
      counterSteps bits+2*potential (increment bits)=4+2*potential bits ∧
      (∀ n, totalCounterSteps n bits ≤ 4*n+2*potential bits ∧
        BinaryAdder.littleVal (iterateCounter n bits)=BinaryAdder.littleVal bits+n) := by sorry
