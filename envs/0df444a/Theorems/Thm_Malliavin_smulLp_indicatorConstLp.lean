-- Prove2me | Theorems.Thm_Malliavin_smulLp_indicatorConstLp
-- name    : Malliavin.smulLp_indicatorConstLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:54:19.471381+00:00
-- url     : https://prove2.me/theorems/56ebdfc4-0dda-41f5-9d94-ca79829f202f
-- title:
--   Malliavin: smul Lp indicator Const Lp
-- statement:
--   The Malliavin construction uses the smul Lp indicator Const Lp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/FubiniLift.lean#L237-L245
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/FubiniLift.lean#L237-L245

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
variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] {μ : Measure Ω} {ν : Measure T}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Malliavin.smulLp_indicatorConstLp (e : E) {A : Set Ω} (hA : MeasurableSet A)
    (hμA : μ A ≠ ∞) (c : ℝ) :
    smulLp e (indicatorConstLp 2 hA hμA c) = indicatorConstLp 2 hA hμA (c • e) := by sorry
