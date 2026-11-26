-- Prove2me | Theorems.Thm_Malliavin_naturalItoDuality_wienerIntegral
-- name    : Malliavin.naturalItoDuality_wienerIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:37:21.380798+00:00
-- url     : https://prove2.me/theorems/c5d68379-32f1-4b25-8a61-b0f7ad90dd13
-- title:
--   Malliavin: natural Ito Duality wiener Integral
-- statement:
--   **Malliavin--Itô duality for the constructed integral on the first chaos**, against an
--   arbitrary predictable integrand.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoDuality.lean#L150-L173
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoDuality.lean#L150-L173

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

theorem Malliavin.naturalItoDuality_wienerIntegral
    (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure)
    (U : PredictableProcessL2 𝓅 P) :
    inner ℝ (wienerIntegral hB g - expectationL2 (wienerIntegral hB g))
        (naturalItoIntegral hB hsm hnat U) =
      inner ℝ (predictableProjection 𝓅
        (timeDerivative hB L hL hgen
          (mderivClosure P (wienerIntegral hB g)))) U := by sorry
