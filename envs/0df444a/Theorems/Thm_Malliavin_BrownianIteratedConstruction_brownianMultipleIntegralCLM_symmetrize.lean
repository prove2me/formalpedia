-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianMultipleIntegralCLM_symmetrize
-- name    : Malliavin.BrownianIteratedConstruction.brownianMultipleIntegralCLM_symmetrize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:23:23.731107+00:00
-- url     : https://prove2.me/theorems/27334611-3670-5032-b84d-e9bd93cd8460
-- title:
--   Brownian Iterated Construction: brownian Multiple Integral CLM symmetrize
-- statement:
--   The canonical Brownian multiple operator only depends on the symmetric part of its kernel.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegral.lean#L51-L57
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegral.lean#L51-L57

import Definitions.Def_Malliavin_BrownianChaosHilbertSum
import Definitions.Def_Malliavin_BrownianMultipleIntegral
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
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.BrownianIteratedConstruction.brownianMultipleIntegralCLM_symmetrize
    (hB : IsPreBrownianReal B P) (n : ℕ) (f : IteratedKernel n) :
    brownianMultipleIntegralCLM hB n
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f) =
      brownianMultipleIntegralCLM hB n f := by sorry
