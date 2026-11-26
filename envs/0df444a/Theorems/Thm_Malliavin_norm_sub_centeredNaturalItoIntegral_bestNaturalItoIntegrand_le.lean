-- Prove2me | Theorems.Thm_Malliavin_norm_sub_centeredNaturalItoIntegral_bestNaturalItoIntegrand_le
-- name    : Malliavin.norm_sub_centeredNaturalItoIntegral_bestNaturalItoIntegrand_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:54:18.549545+00:00
-- url     : https://prove2.me/theorems/75a64458-ce6b-5b78-9c23-9e123764ac14
-- title:
--   Malliavin: norm sub centered Natural Ito Integral best Natural Ito Integrand le
-- statement:
--   The best integrand minimizes the centered `L²` reconstruction error among all predictable
--   integrands.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L300-L327
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L300-L327

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

theorem Malliavin.norm_sub_centeredNaturalItoIntegral_bestNaturalItoIntegrand_le
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (G : (CameronMartin.expectationMap P).ker)
    (U : PredictableProcessL2 𝓅 P) :
    ‖G - centeredNaturalItoIntegralIsometry hB hsm hnat
        (bestNaturalItoIntegrand hB hsm hnat G)‖ ≤
      ‖G - centeredNaturalItoIntegralIsometry hB hsm hnat U‖ := by sorry
