-- Prove2me | Theorems.Thm_Malliavin_sub_expectationL2_eq_naturalItoIntegral_predictableProjection
-- name    : Malliavin.sub_expectationL2_eq_naturalItoIntegral_predictableProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:38:24.437852+00:00
-- url     : https://prove2.me/theorems/5f03e972-b32e-4853-aeb7-04d50321ef12
-- title:
--   Malliavin: sub expectation L2 eq natural Ito Integral predictable Projection
-- statement:
--   Centered form of the concrete conditional Clark--Ocone formula.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoDuality.lean#L285-L303
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoDuality.lean#L285-L303

import Definitions.Def_Malliavin_NaturalItoRange
import Definitions.Def_Malliavin_ClarkOconeExamples
import Definitions.Def_Malliavin_NaturalItoDuality
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

theorem Malliavin.sub_expectationL2_eq_naturalItoIntegral_predictableProjection
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hMRT : NaturalMartingaleRepresentation hB hsm hnat)
    (F : D12 P)
    (hBest : bestNaturalItoIntegrand hB hsm hnat (centeredPartL2 F.1) =
      predictableProjection 𝓅
        (timeDerivative hB coordinate coordinate_apply generated
          (mderivD12 P F))) :
    F.1 - expectationL2 F.1 = naturalItoIntegral hB hsm hnat
      (predictableProjection 𝓅
        (timeDerivative hB coordinate coordinate_apply generated
          (mderivD12 P F))) := by sorry
