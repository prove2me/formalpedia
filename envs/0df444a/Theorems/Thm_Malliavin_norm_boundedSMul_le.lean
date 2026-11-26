-- Prove2me | Theorems.Thm_Malliavin_norm_boundedSMul_le
-- name    : Malliavin.norm_boundedSMul_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:06:30.771955+00:00
-- url     : https://prove2.me/theorems/4d5f91e3-44c1-549b-8696-a679db694fd0
-- title:
--   Malliavin: norm bounded SMul le
-- statement:
--   The Malliavin construction uses the norm bounded SMul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/FubiniLift.lean#L724-L726
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/FubiniLift.lean#L724-L726

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

theorem Malliavin.norm_boundedSMul_le {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) {C : ℝ}
    (hC : ∀ x, |G x| ≤ C) (U : Lp E 2 μ) : ‖boundedSMul hG hC U‖ ≤ C * ‖U‖ := by sorry
