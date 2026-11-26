-- Prove2me | Theorems.Thm_Malliavin_coeFn_boundedSMul
-- name    : Malliavin.coeFn_boundedSMul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:51:28.975801+00:00
-- url     : https://prove2.me/theorems/b407d99e-afbf-5246-8874-c7504b350b25
-- title:
--   Malliavin: coe Fn bounded SMul
-- statement:
--   The Malliavin construction uses the coe Fn bounded SMul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/FubiniLift.lean#L728-L731
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/FubiniLift.lean#L728-L731

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

theorem Malliavin.coeFn_boundedSMul {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) {C : ℝ}
    (hC : ∀ x, |G x| ≤ C) (U : Lp E 2 μ) :
    (boundedSMul hG hC U : Ω → E) =ᵐ[μ] fun x ↦ G x • U x := by sorry
