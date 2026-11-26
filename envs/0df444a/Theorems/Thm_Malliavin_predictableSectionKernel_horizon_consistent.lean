-- Prove2me | Theorems.Thm_Malliavin_predictableSectionKernel_horizon_consistent
-- name    : Malliavin.predictableSectionKernel_horizon_consistent
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:43:19.228794+00:00
-- url     : https://prove2.me/theorems/0175969c-66b1-4cb9-95e4-5747dff405b7
-- title:
--   Malliavin: predictable Section Kernel horizon consistent
-- statement:
--   **Horizon consistency**: the predictable-section kernels for two horizons agree on the
--   smaller one, almost every time and almost surely — both are the fixed-time kernel.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/KernelIdentification.lean#L353-L374
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/KernelIdentification.lean#L353-L374

import Definitions.Def_Malliavin_PredictableKernel
import Definitions.Def_Malliavin_TimewiseCondExp
import Definitions.Def_Malliavin_NaturalFiltrationLeftContinuous
import Mathlib.MeasureTheory.Function.Floor
import Definitions.Def_Malliavin_KernelIdentification
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

theorem Malliavin.predictableSectionKernel_horizon_consistent
    (hB : IsPreBrownianReal B P) (hm : ∀ s, StronglyMeasurable (B s))
    (hgen : IsWienerGenerated B) {T₁ T₂ : ℝ≥0} (h : T₁ ≤ T₂) :
    ∀ᵐ t ∂finiteHorizonTimeMeasure T₁, 0 < t →
      ∀ᵐ w ∂P,
        predictableSectionKernel (finiteHorizonProductMeasure P T₁)
            (Filtration.natural B hm) (t, w)
          = predictableSectionKernel (finiteHorizonProductMeasure P T₂)
              (Filtration.natural B hm) (t, w) := by sorry
