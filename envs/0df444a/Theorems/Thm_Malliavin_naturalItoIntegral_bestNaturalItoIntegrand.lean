-- Prove2me | Theorems.Thm_Malliavin_naturalItoIntegral_bestNaturalItoIntegrand
-- name    : Malliavin.naturalItoIntegral_bestNaturalItoIntegrand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:49:45.345577+00:00
-- url     : https://prove2.me/theorems/f9941d66-ccf6-4054-ac88-c102af38b531
-- title:
--   Malliavin: natural Ito Integral best Natural Ito Integrand
-- statement:
--   Integrating the best integrand gives exactly the ambient value of the range projection.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L169-L184
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L169-L184

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

theorem Malliavin.naturalItoIntegral_bestNaturalItoIntegrand
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (G : (CameronMartin.expectationMap P).ker) :
    naturalItoIntegral hB hsm hnat (bestNaturalItoIntegrand hB hsm hnat G) =
      (((centeredNaturalItoRangeProjection hB hsm hnat G :
        centeredNaturalItoRange hB hsm hnat) :
          (CameronMartin.expectationMap P).ker) : RandomL2 P) := by sorry
