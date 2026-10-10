-- Prove2me | Theorems.Thm_IntMul_StreamCarryStep_stream_carry_step
-- name    : IntMul.StreamCarryStep.stream_carry_step
-- status  : Open
-- author  : @raresbuhai
-- created : 2026-10-10T11:05:21.772856+00:00
-- url     : https://prove2.me/theorems/dafd37e1-efa2-4419-a569-177c05fa22dc
-- title:
--   Complete actual streaming coefficient ingestion, carry arithmetic and digit append
-- statement:
--   Let pre, x, tail, a, y, z and l be arbitrary binary words. Assume |x|=|y|=n=val(l)+1, put B=val(z)+1 and assume B≤n+1. From its explicit prepared incoming caller frame, the fixed fifteen-tape machine reads the next coefficient x at the interior root-input cursor, physically builds the x#y request using the previous carry y, performs the actual padded carry update, and appends the emitted low digit to the saved output prefix a. It halts at its exact complete terminal configuration after some number t of actual transitions with
--
--   $$t\le19n+12B+12|z|+4|l|+50.$$
--
--   The appended low digit is little-endian and has value (val(x)+val(y)) mod 2^B. Bank 11 contains the exact canonical n-bit next carry word for floor((val(x)+val(y))/2^B). The read-only root input pre++x++tail#l is preserved, with its cursor advanced by n; the output cursor advances by B. All fifteen tape contents and heads, the retained previous carry and restored width templates are specified. Every opening, delimiter write, copy, rewind, arithmetic transition and four caller returns is counted. The bound is independent of the earlier input and output prefix lengths. Descriptor, previous-carry and cursor preparation remain explicit caller obligations.
-- source:
--   Original complete physical streaming carry update. Privately owns literal bank embeddings, ingestion opening, request construction and rewind, digit append, full-frame handoffs and clock composition. Uses accepted interior reader, canonical padded-carry arithmetic and finite-caller simulation. Written by Codex.

import Definitions.Def_IntMul_StreamCarryStep
import Mathlib.Tactic
import Theorems.Thm_IntMul_FramedBlockRead_read_block
import Theorems.Thm_IntMul_PaddedCarryStep_padded_carry_step
import Theorems.Thm_IntMul_FiniteCaller_simulate_run

open IntMul IntMul.StreamCarryStep

theorem IntMul.StreamCarryStep.stream_carry_step (pre x tail a y z l : List Bool)
    (h : x.length=y.length) (hn : x.length=val l+1)
    (hB : CarryStep.blockSize z ≤ x.length+1) :
    ∃ t : ℕ, t ≤ 19*x.length+12*CarryStep.blockSize z+12*z.length+4*l.length+50 ∧
      machine.step^[t] (initialFrame pre x tail a y z l)=finalFrame pre x tail a y z l ∧
      (machine.step^[t] (initialFrame pre x tail a y z l)).state=machine.qHalt ∧
      val (CarryStep.digitWord x y z).reverse=(val x+val y)%(2^CarryStep.blockSize z) ∧
      val (PaddedCarryStep.nextCarryWord x y z)=(val x+val y)/(2^CarryStep.blockSize z) := by sorry
