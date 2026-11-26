-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPositiveTowerLI_mem_naturalItoRange
-- name    : Malliavin.BrownianIteratedConstruction.brownianPositiveTowerLI_mem_naturalItoRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:23:16.977729+00:00
-- url     : https://prove2.me/theorems/c9b8d8da-ec80-5a27-adf2-97aa85c6e95b
-- title:
--   Brownian Iterated Construction: brownian Positive Tower LI mem natural Ito Range
-- statement:
--   Every value of the global canonical positive tower is a natural Itô terminal value.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaosHilbertSum.lean#L135-L149
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaosHilbertSum.lean#L135-L149

import Definitions.Def_Malliavin_BrownianChaosTotality
import Definitions.Def_Malliavin_BrownianChaosHilbertSum
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.BrownianIteratedConstruction.brownianPositiveTowerLI_mem_naturalItoRange
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (f : IteratedIntegralConstruction.PositiveKernelSum) :
    brownianPositiveTowerLI hB hsm f ∈ naturalItoRange hB hsm hnat := by sorry
