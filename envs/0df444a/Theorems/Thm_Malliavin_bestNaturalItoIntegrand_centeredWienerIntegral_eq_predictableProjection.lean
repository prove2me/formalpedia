-- Prove2me | Theorems.Thm_Malliavin_bestNaturalItoIntegrand_centeredWienerIntegral_eq_predictableProjection
-- name    : Malliavin.bestNaturalItoIntegrand_centeredWienerIntegral_eq_predictableProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:37:19.330461+00:00
-- url     : https://prove2.me/theorems/c2f6f4b6-1583-5fcc-80dd-895b5425856c
-- title:
--   Malliavin: best Natural Ito Integrand centered Wiener Integral eq predictable Projection
-- statement:
--   On the first chaos, the canonical best Itô integrand is exactly the predictable projection
--   of the time-realized Malliavin derivative. Both are the deterministic kernel `g`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoDuality.lean#L56-L69
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoDuality.lean#L56-L69

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

theorem Malliavin.bestNaturalItoIntegrand_centeredWienerIntegral_eq_predictableProjection
    (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    bestNaturalItoIntegrand hB hsm hnat (centeredWienerIntegral hB g) =
      predictableProjection 𝓅
        (timeDerivative hB L hL hgen
          (mderivClosure P (wienerIntegral hB g))) := by sorry
