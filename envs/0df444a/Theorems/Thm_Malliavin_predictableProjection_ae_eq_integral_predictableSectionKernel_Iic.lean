-- Prove2me | Theorems.Thm_Malliavin_predictableProjection_ae_eq_integral_predictableSectionKernel_Iic
-- name    : Malliavin.predictableProjection_ae_eq_integral_predictableSectionKernel_Iic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:23:45.870837+00:00
-- url     : https://prove2.me/theorems/ff1f2dd8-4341-4019-9da4-13ca26488164
-- title:
--   Malliavin: predictable Projection ae eq integral predictable Section Kernel Iic
-- statement:
--   On a finite horizon, the predictable projection is a pointwise integral of the same-time
--   section `U (p.1, ·)` against the jointly predictable sample-space kernel
--   `predictableSectionKernel`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableKernel.lean#L224-L240
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableKernel.lean#L224-L240

import Definitions.Def_Malliavin_ClarkOcone
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Composition.MapComap
import Definitions.Def_Malliavin_PredictableKernel
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]

theorem Malliavin.predictableProjection_ae_eq_integral_predictableSectionKernel_Iic
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (U : TimeProcessL2 P) (T : ℝ≥0) :
    (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ)
      =ᵐ[finiteHorizonProductMeasure P T]
        fun p => ∫ w, U (p.1, w)
          ∂predictableSectionKernel (finiteHorizonProductMeasure P T) 𝓕 p := by sorry
