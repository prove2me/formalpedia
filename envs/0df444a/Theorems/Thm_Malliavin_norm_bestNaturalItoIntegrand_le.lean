-- Prove2me | Theorems.Thm_Malliavin_norm_bestNaturalItoIntegrand_le
-- name    : Malliavin.norm_bestNaturalItoIntegrand_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:54:02.004368+00:00
-- url     : https://prove2.me/theorems/d9e2b5e9-4a32-53e7-b282-328e9788df79
-- title:
--   Malliavin: norm best Natural Ito Integrand le
-- statement:
--   The best-integrand operator is contractive.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L188-L200
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L188-L200

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

theorem Malliavin.norm_bestNaturalItoIntegrand_le
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (G : (CameronMartin.expectationMap P).ker) :
    ‖bestNaturalItoIntegrand hB hsm hnat G‖ ≤ ‖G‖ := by sorry
