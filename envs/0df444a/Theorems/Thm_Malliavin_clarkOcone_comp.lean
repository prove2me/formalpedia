-- Prove2me | Theorems.Thm_Malliavin_clarkOcone_comp
-- name    : Malliavin.clarkOcone_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:39:34.143281+00:00
-- url     : https://prove2.me/theorems/56f67f12-e5cf-4bdf-9ca8-9d5c4e8f835e
-- title:
--   Malliavin: clark Ocone comp
-- statement:
--   **Clark--Ocone for `φ (F)`, `F ∈ 𝔻₁,₂` arbitrary**:
--   `φ (F) = E[φ (F)] + C.itoIntegral (Π (φ' (F) Dₜ F))`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L381-L394
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L381-L394

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

theorem Malliavin.clarkOcone_comp {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : ContDiff ℝ 1 φ)
    (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) (F : D12 P) :
    (D12.comp P hφ hK F : Lp ℝ 2 P) =
      expectationL2 (D12.comp P hφ hK F : Lp ℝ 2 P) +
        C.itoIntegral (predictableProjection 𝓕 (boundedSMul
          (aestronglyMeasurable_comp_snd (ν := nonnegativeLebesgueMeasure)
            (hφ.continuous_deriv_one.comp_aestronglyMeasurable
              (Lp.aestronglyMeasurable (F : Lp ℝ 2 P))))
          (C := K) (fun p ↦ by rw [← Real.norm_eq_abs]; exact_mod_cast hK ((F : Lp ℝ 2 P) p.2))
          (C.timeDerivative (mderivD12 P F)))) := by sorry
