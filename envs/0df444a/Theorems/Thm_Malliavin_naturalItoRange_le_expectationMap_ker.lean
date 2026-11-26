-- Prove2me | Theorems.Thm_Malliavin_naturalItoRange_le_expectationMap_ker
-- name    : Malliavin.naturalItoRange_le_expectationMap_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:51:18.999788+00:00
-- url     : https://prove2.me/theorems/339952f9-e33e-4913-a7fa-2e2e7981541e
-- title:
--   Malliavin: natural Ito Range le expectation Map ker
-- statement:
--   Every natural Itô terminal value is centered.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L50-L56
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L50-L56

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

theorem Malliavin.naturalItoRange_le_expectationMap_ker
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    naturalItoRange hB hsm hnat ≤ (CameronMartin.expectationMap P).ker := by sorry
