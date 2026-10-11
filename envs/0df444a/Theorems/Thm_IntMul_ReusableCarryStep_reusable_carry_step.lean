-- Prove2me | Theorems.Thm_IntMul_ReusableCarryStep_reusable_carry_step
-- name    : IntMul.ReusableCarryStep.reusable_carry_step
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T12:22:17.939235+00:00
-- url     : https://prove2.me/theorems/dbba41b5-e3ae-41e5-9c1d-94f64ddec5e0
-- title:
--   Complete reusable physical coefficient carry update and linear workspace cleanup
-- statement:
--   Let pre, x, tail, a, y, z and l be binary words, with |x|=|y|=n=val(l)+1, B=val(z)+1 and B≤n+1. From the explicit prepared incoming caller frame, one fixed fifteen-tape machine reads the next coefficient x, performs the actual carry arithmetic, appends the little-endian low digit to output a, physically erases the old saved carry, returns the canonical n-bit next carry to bank 12, physically erases all nine temporary arithmetic banks, and rewinds the retained B descriptor. It reaches its exact complete final frame and halts after some actual transition count t satisfying
--
--   $$t\le41n+13B+21|z|+4|l|+125.$$
--
--   The low digit has value (val(x)+val(y)) mod 2^B, and the saved canonical next carry has value floor((val(x)+val(y))/2^B). The read-only root input is retained with its cursor advanced by n. Output a is retained with the low digit appended and its cursor advanced by B. Both width templates are restored. Descriptor bank 6 and saved-carry bank 12 have their heads at zero. All nine temporary banks are empty marked tapes with heads zero. These exact cells and heads are ready for the next streaming coefficient at a charged finite-caller restart. All physical copying, erasures, rewinds and thirteen caller returns are included. The bound is independent of the earlier input and output prefix lengths. Descriptor and incoming-cursor preparation remain explicit caller obligations.
-- source:
--   Original complete reusable physical streaming carry update. Privately owns native state embeddings, physical carry return, finite selected-bank erasure composition, full retained-frame handoffs, all nine cleanup clocks and descriptor rewind. Uses accepted streaming carry, physical bank erasure and finite-caller simulation. Written by Codex.

import Definitions.Def_IntMul_ReusableCarryStep
import Mathlib.Tactic
import Theorems.Thm_IntMul_TapeBankErase_erase_bank
import Theorems.Thm_IntMul_FiniteCaller_simulate_run
import Theorems.Thm_IntMul_StreamCarryStep_stream_carry_step

open IntMul IntMul.ReusableCarryStep

theorem IntMul.ReusableCarryStep.reusable_carry_step (pre x tail a y z l : List Bool)
    (h : x.length=y.length) (hn : x.length=val l+1)
    (hB : CarryStep.blockSize z ≤ x.length+1) :
    ∃ t : ℕ, t ≤ 41*x.length+13*CarryStep.blockSize z+21*z.length+4*l.length+125 ∧
      machine.step^[t] (initialFrame pre x tail a y z l)=finalFrame pre x tail a y z l ∧
      (machine.step^[t] (initialFrame pre x tail a y z l)).state=machine.qHalt ∧
      val (CarryStep.digitWord x y z).reverse=(val x+val y)%(2^CarryStep.blockSize z) ∧
      val (PaddedCarryStep.nextCarryWord x y z)=(val x+val y)/(2^CarryStep.blockSize z) := by sorry
