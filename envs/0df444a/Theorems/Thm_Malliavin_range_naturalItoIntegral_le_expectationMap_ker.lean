-- Prove2me | Theorems.Thm_Malliavin_range_naturalItoIntegral_le_expectationMap_ker
-- name    : Malliavin.range_naturalItoIntegral_le_expectationMap_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:48:35.739344+00:00
-- url     : https://prove2.me/theorems/57933c84-1cbe-583e-9946-6d9fae72802c
-- title:
--   Malliavin: range natural Ito Integral le expectation Map ker
-- statement:
--   Every terminal value of the constructed Itô integral is centered.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L344-L354
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L344-L354

import Definitions.Def_Malliavin_ItoConstruction
import Definitions.Def_Malliavin_ItoConsequences
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

theorem Malliavin.range_naturalItoIntegral_le_expectationMap_ker
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    LinearMap.range (naturalItoIntegral hB hsm hnat).toLinearMap ≤
      (CameronMartin.expectationMap P).ker := by sorry
