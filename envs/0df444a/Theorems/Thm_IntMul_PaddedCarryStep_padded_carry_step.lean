-- Prove2me | Theorems.Thm_IntMul_PaddedCarryStep_padded_carry_step
-- name    : IntMul.PaddedCarryStep.padded_carry_step
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T10:37:47.776167+00:00
-- url     : https://prove2.me/theorems/af0f3027-7c9a-44e5-a28a-d8a7653cb4f8
-- title:
--   Actual bounded-carry update with canonical next operand and complete linear clock
-- statement:
--   Let x and y be arbitrary binary words of the same length n, and let z be a binary descriptor of length w. Put B=val(z)+1 and assume B≤n+1. From its specified incoming frame, with a descriptor bank already prepared by the caller, the fixed ten-tape machine halts at its exact complete terminal frame after some number t of actual transitions satisfying
--
--   $$t\le 10n+10B+12w+36.$$
--
--   The retained low digit, emitted little-endian, has numerical value
--
--   $$d=(\operatorname{val}(x)+\operatorname{val}(y))\bmod 2^B.$$
--
--   The new outgoing carry bank contains the exact canonical n-bit word for
--
--   $$c=\left\lfloor\frac{\operatorname{val}(x)+\operatorname{val}(y)}{2^B}\right\rfloor.$$
--
--   This canonical word is in usual most-significant-first order and can serve directly as an equal-width operand in the next carry update. Every padding zero, countdown and template-reset transition, backward copy, and caller return is charged. All ten tape contents and heads are specified; the original read-only input and the emitted digit are preserved. Leading zeroes, zero-width operands and the boundary B=n+1 are included under the stated hypotheses. Descriptor preparation remains an explicit caller cost.
-- source:
--   Original physical canonical carry continuation. Privately owns zero generation, countdown/reset, literal embeddings, backward copy and full-frame composition. Uses accepted actual carry arithmetic and finite-caller simulation. Countdown arithmetic derives from the pinned Apache-2.0 integer-mult-bounds material attributed in the counted-stream development. Written by Codex.

import Definitions.Def_IntMul_BinaryAdder
import Definitions.Def_IntMul_MultitapeModel
import Mathlib.Tactic
import Mathlib.Data.Nat.Bits
import Definitions.Def_IntMul_CountedStream
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Definitions.Def_IntMul_PaddedCarryStep
import Theorems.Thm_IntMul_CarryStep_carry_step
import Theorems.Thm_IntMul_FiniteCaller_simulate_run

open IntMul IntMul.PaddedCarryStep

theorem IntMul.PaddedCarryStep.padded_carry_step (x y z : List Bool) (h : x.length=y.length)
    (hB : CarryStep.blockSize z ≤ x.length+1) :
    ∃ t : ℕ, t ≤ 10*x.length+10*CarryStep.blockSize z+12*z.length+36 ∧
      machine.step^[t] (initialFrame x y z)=finalFrame x y z ∧
      (machine.step^[t] (initialFrame x y z)).state=machine.qHalt ∧
      val (CarryStep.digitWord x y z).reverse=(val x+val y)%(2^CarryStep.blockSize z) ∧
      val (nextCarryWord x y z)=(val x+val y)/(2^CarryStep.blockSize z) := by sorry
