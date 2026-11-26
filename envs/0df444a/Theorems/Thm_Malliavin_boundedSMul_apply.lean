-- Prove2me | Theorems.Thm_Malliavin_boundedSMul_apply
-- name    : Malliavin.boundedSMul_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:06:25.644347+00:00
-- url     : https://prove2.me/theorems/1a189510-2d0e-5270-9263-c6c6aa5376ff
-- title:
--   Malliavin: bounded SMul apply
-- statement:
--   The Malliavin construction uses the bounded SMul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/FubiniLift.lean#L720-L722
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/FubiniLift.lean#L720-L722

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_FubiniLift
set_option autoImplicit false
open MeasureTheory Filter Topology Function
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3
open Malliavin
variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [NormedAddCommGroup E]
  [NormedSpace ℝ E]

theorem Malliavin.boundedSMul_apply {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) {C : ℝ}
    (hC : ∀ x, |G x| ≤ C) (U : Lp E 2 μ) :
    boundedSMul hG hC U = (memLp_boundedSMul hG hC U).toLp _ := by sorry
