-- Prove2me | Theorems.Thm_IntMul_CarryStep_carry_step
-- name    : IntMul.CarryStep.carry_step
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T10:05:11.102673+00:00
-- url     : https://prove2.me/theorems/e3764905-97cd-42de-9259-98c06f2ffef8
-- title:
--   Actual local bounded-carry arithmetic with digit, outgoing carry and complete linear clock
-- statement:
--   Let x and y be arbitrary binary words of the same length n, and let z be a binary descriptor of length w. Put B=val(z)+1 and assume B≤n+1. Starting from the specified incoming arithmetic frame, whose descriptor bank has already been prepared by a caller, the fixed nine-tape machine halts at the exact complete terminal frame after some number t of actual transitions satisfying
--
--   $$t\le 9n+5B+8w+28.$$
--
--   Writing the emitted digit and carry in their usual numerical order, their values are respectively
--
--   $$d=(\operatorname{val}(x)+\operatorname{val}(y))\bmod 2^B,
--   \qquad c=\left\lfloor\frac{\operatorname{val}(x)+\operatorname{val}(y)}{2^B}\right\rfloor.$$
--
--   Both words are emitted little-endian on distinct banks. The complete frame specifies the retained input and sum, work operand, descriptor, routed sum request, restored countdown templates and all nine final heads. All arithmetic, copying, rewinding, countdown transitions and four caller returns are charged. Leading zeroes, zero-width operands and B=n+1 are included whenever the stated hypotheses hold. This implements one local carry update for exact coefficient normalization; preparing the incoming descriptor is an explicit caller cost.
-- source:
--   Original complete actual carry arithmetic. Privately owns full native addition, countdown/reset, relay, numerical splitting and complete configuration proofs. Countdown arithmetic uses the pinned Apache-2.0 CrocSwap/integer-mult-bounds source attributed in the counted-stream development. Written by Codex.

import Definitions.Def_IntMul_CarryStep
import Definitions.Def_IntMul_BinaryAdder
import Definitions.Def_IntMul_MultitapeModel
import Mathlib.Tactic
import Mathlib.Data.Nat.Bits
import Definitions.Def_IntMul_TapeAdder
import Mathlib.Data.List.GetD
import Definitions.Def_IntMul_CountedStream
import Definitions.Def_IntMul_CountedStreamFrames
import Mathlib.Data.List.TakeDrop
import Theorems.Thm_IntMul_FiniteCaller_simulate_run

open IntMul IntMul.CarryStep

theorem IntMul.CarryStep.carry_step (x y z : List Bool) (h : x.length=y.length)
    (hB : blockSize z ≤ x.length+1) :
    ∃ t : ℕ, t ≤ 9*x.length+5*blockSize z+8*z.length+28 ∧
      machine.step^[t] (initialFrame x y z)=finalFrame x y z ∧
      (machine.step^[t] (initialFrame x y z)).state=machine.qHalt ∧
      val (digitWord x y z).reverse=(val x+val y)%(2^blockSize z) ∧
      val (carryWord x y z).reverse=(val x+val y)/(2^blockSize z) := by sorry
