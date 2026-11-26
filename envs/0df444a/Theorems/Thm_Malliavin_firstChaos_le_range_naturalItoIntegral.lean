-- Prove2me | Theorems.Thm_Malliavin_firstChaos_le_range_naturalItoIntegral
-- name    : Malliavin.firstChaos_le_range_naturalItoIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:50:49.899495+00:00
-- url     : https://prove2.me/theorems/c8a39e6a-7554-51ad-8777-3ff3b79ff6e8
-- title:
--   Malliavin: first Chaos le range natural Ito Integral
-- statement:
--   In particular, the range of the constructed Itô integral contains the entire first chaos.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L358-L366
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L358-L366

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

theorem Malliavin.firstChaos_le_range_naturalItoIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    firstChaos hB ≤
      LinearMap.range (naturalItoIntegral hB hsm hnat).toLinearMap := by sorry
