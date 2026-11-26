-- Prove2me | Theorems.Thm_Malliavin_timeDerivative_mderivClosure_comp
-- name    : Malliavin.timeDerivative_mderivClosure_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:39:35.668901+00:00
-- url     : https://prove2.me/theorems/060a86c0-3e72-5224-9b5f-00e007cdd34f
-- title:
--   Malliavin: time Derivative mderiv Closure comp
-- statement:
--   **The time-form chain rule**: `Dₜ φ (F) = φ' (F) Dₜ F` for every `F ∈ 𝔻₁,₂` and `φ` of class
--   `C¹` with bounded derivative, as an identity in `L²(ℝ≥0 × W)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L969-L977
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L969-L977

import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_ChainRule
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
  {φ : ℝ → ℝ} {K : ℝ≥0}

theorem Malliavin.timeDerivative_mderivClosure_comp (hB : IsPreBrownianReal B P)
    (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) {F : Lp ℝ 2 P} (hF : F ∈ domD12 P) :
    timeDerivative hB L hL hgen (mderivClosure P ((memLp_comp_of_deriv_le P hφ hK F).toLp _)) =
      boundedSMul (aestronglyMeasurable_comp_snd (ν := nonnegativeLebesgueMeasure)
          (hφ.continuous_deriv_one.comp_aestronglyMeasurable (Lp.aestronglyMeasurable F)))
        (C := K) (fun p ↦ by rw [← Real.norm_eq_abs]; exact_mod_cast hK (F p.2))
        (timeDerivative hB L hL hgen (mderivClosure P F)) := by sorry
