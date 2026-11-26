-- Prove2me | Theorems.Thm_Malliavin_predictableDerivative_comp
-- name    : Malliavin.predictableDerivative_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:36:04.703585+00:00
-- url     : https://prove2.me/theorems/158b7b06-783b-5cc3-add6-904afcaa1b46
-- title:
--   Malliavin: predictable Derivative comp
-- statement:
--   **The Clark--Ocone integrand of `φ (F)`** for an arbitrary `F ∈ 𝔻₁,₂` is the predictable
--   projection of `φ' (F) Dₜ F`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L351-L364
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L351-L364

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

theorem Malliavin.predictableDerivative_comp {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : ContDiff ℝ 1 φ)
    (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) (F : D12 P) :
    predictableDerivative C (D12.comp P hφ hK F) =
      predictableProjection 𝓕 (boundedSMul
        (aestronglyMeasurable_comp_snd (ν := nonnegativeLebesgueMeasure)
          (hφ.continuous_deriv_one.comp_aestronglyMeasurable
            (Lp.aestronglyMeasurable (F : Lp ℝ 2 P))))
        (C := K) (fun p ↦ by rw [← Real.norm_eq_abs]; exact_mod_cast hK ((F : Lp ℝ 2 P) p.2))
        (C.timeDerivative (mderivD12 P F))) := by sorry
