-- Prove2me | Theorems.Thm_Malliavin_firstChaos_le_naturalItoRange
-- name    : Malliavin.firstChaos_le_naturalItoRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:54:08.481789+00:00
-- url     : https://prove2.me/theorems/010de1cd-cb5d-46fb-a446-b703561e8617
-- title:
--   Malliavin: first Chaos le natural Ito Range
-- statement:
--   The natural Itô terminal-value subspace contains the full Gaussian first chaos.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L60-L66
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L60-L66

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

theorem Malliavin.firstChaos_le_naturalItoRange
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    firstChaos hB ≤ naturalItoRange hB hsm hnat := by sorry
