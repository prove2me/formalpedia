-- Prove2me | Theorems.Thm_Malliavin_centeredNaturalItoIntegral_bestNaturalItoIntegrand
-- name    : Malliavin.centeredNaturalItoIntegral_bestNaturalItoIntegrand
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:49:36.544793+00:00
-- url     : https://prove2.me/theorems/f3d22d40-2879-491c-8ac4-3d0f7cdedd7e
-- title:
--   Malliavin: centered Natural Ito Integral best Natural Ito Integrand
-- statement:
--   Under martingale representation, the best integrand recovers every centered terminal
--   variable exactly.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L358-L377
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L358-L377

import Definitions.Def_Malliavin_ItoConsequences
import Definitions.Def_Malliavin_NaturalItoRange
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
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.centeredNaturalItoIntegral_bestNaturalItoIntegrand
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hMRT : NaturalMartingaleRepresentation hB hsm hnat)
    (G : (CameronMartin.expectationMap P).ker) :
    centeredNaturalItoIntegralIsometry hB hsm hnat
      (bestNaturalItoIntegrand hB hsm hnat G) = G := by sorry
