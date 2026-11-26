-- Prove2me | Theorems.Thm_Malliavin_predictableProjection_ae_eq_sameTimeCondExpKernel_Iic
-- name    : Malliavin.predictableProjection_ae_eq_sameTimeCondExpKernel_Iic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:25:01.430721+00:00
-- url     : https://prove2.me/theorems/cb3d56b1-ba19-41e5-a9f4-348e7540e250
-- title:
--   Malliavin: predictable Projection ae eq same Time Cond Exp Kernel Iic
-- statement:
--   Same-time form of `predictableProjection_ae_eq_integral_condExpKernel_Iic`: the conditional
--   kernel can be used after replacing the input time by the observed time `p.1`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableKernel.lean#L208-L219
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableKernel.lean#L208-L219

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

theorem Malliavin.predictableProjection_ae_eq_sameTimeCondExpKernel_Iic
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (U : TimeProcessL2 P) (T : ℝ≥0) :
    (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ)
      =ᵐ[finiteHorizonProductMeasure P T]
        fun p => ∫ q, U (p.1, q.2)
          ∂condExpKernel (finiteHorizonProductMeasure P T) 𝓕.predictable p := by sorry
