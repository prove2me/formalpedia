-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickPowerLp_mem_domD12
-- name    : Malliavin.BrownianIteratedConstruction.brownianWickPowerLp_mem_domD12
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:21:17.747659+00:00
-- url     : https://prove2.me/theorems/698c57b6-bacf-5778-831a-322617255824
-- title:
--   Brownian Iterated Construction: brownian Wick Power Lp mem dom D12
-- statement:
--   A Wick power of a formal Brownian step sum belongs to the first Malliavin Sobolev space
--   when the Brownian coordinates are continuous linear functionals.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerDuality.lean#L80-L110
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerDuality.lean#L80-L110

import Definitions.Def_Malliavin_BrownianWickPurePowerComparison
import Definitions.Def_Malliavin_BrownianMultipleIntegralBoxSpan
import Definitions.Def_Malliavin_PastCylinderDensity
import Definitions.Def_Malliavin_BrownianPurePowerDuality
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

theorem Malliavin.BrownianIteratedConstruction.brownianWickPowerLp_mem_domD12
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    brownianWickPowerLp hB v n ∈ domD12 P := by sorry
