-- Prove2me | Theorems.Thm_Malliavin_norm_comp_sub_expectationL2_eq
-- name    : Malliavin.norm_comp_sub_expectationL2_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:39:32.413691+00:00
-- url     : https://prove2.me/theorems/d94ebba7-3231-468e-b7a1-146f6d2f48c4
-- title:
--   Malliavin: norm comp sub expectation L2 eq
-- statement:
--   **Energy identity for `φ (F)`**: `‖φ (F) - E[φ (F)]‖ = ‖Π (φ' (F) Dₜ F)‖`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L367-L377
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L367-L377

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_CylindricalGrowth
import Definitions.Def_Malliavin_ChainRule
import Definitions.Def_Malliavin_ClarkOconeExamples
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}

theorem Malliavin.norm_comp_sub_expectationL2_eq {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : ContDiff ℝ 1 φ)
    (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) (F : D12 P) :
    ‖(D12.comp P hφ hK F : Lp ℝ 2 P) - expectationL2 (D12.comp P hφ hK F : Lp ℝ 2 P)‖ =
      ‖predictableProjection 𝓕 (boundedSMul
        (aestronglyMeasurable_comp_snd (ν := nonnegativeLebesgueMeasure)
          (hφ.continuous_deriv_one.comp_aestronglyMeasurable
            (Lp.aestronglyMeasurable (F : Lp ℝ 2 P))))
        (C := K) (fun p ↦ by rw [← Real.norm_eq_abs]; exact_mod_cast hK ((F : Lp ℝ 2 P) p.2))
        (C.timeDerivative (mderivD12 P F)))‖ := by sorry
