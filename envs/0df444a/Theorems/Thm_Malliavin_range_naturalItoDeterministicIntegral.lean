-- Prove2me | Theorems.Thm_Malliavin_range_naturalItoDeterministicIntegral
-- name    : Malliavin.range_naturalItoDeterministicIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:50:23.446676+00:00
-- url     : https://prove2.me/theorems/e90b7e51-4d04-54ae-b88d-bada18048c77
-- title:
--   Malliavin: range natural Ito Deterministic Integral
-- statement:
--   The range of the deterministic restriction is precisely the Gaussian first chaos.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L149-L156
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L149-L156

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

theorem Malliavin.range_naturalItoDeterministicIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    LinearMap.range (naturalItoDeterministicIntegral hB hsm hnat).toLinearMap =
      firstChaos hB := by sorry
