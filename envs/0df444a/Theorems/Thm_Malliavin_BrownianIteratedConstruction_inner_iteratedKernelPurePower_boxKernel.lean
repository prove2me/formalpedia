-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_inner_iteratedKernelPurePower_boxKernel
-- name    : Malliavin.BrownianIteratedConstruction.inner_iteratedKernelPurePower_boxKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:25:09.30187+00:00
-- url     : https://prove2.me/theorems/cc132136-e25e-41ba-81af-afa722aace8a
-- title:
--   Brownian Iterated Construction: inner iterated Kernel Pure Power box Kernel
-- statement:
--   Pairing a deterministic pure-power kernel with a box factors into its one-dimensional
--   pairings.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerDuality.lean#L176-L232
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerDuality.lean#L176-L232

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
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.BrownianIteratedConstruction.inner_iteratedKernelPurePower_boxKernel (n : ℕ)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) (u v : Fin n → ℝ≥0) :
    inner ℝ (iteratedKernelPurePower n f) (boxKernel u v) =
      ∏ i, inner ℝ f (iocIndicator (u i) (v i)) := by sorry
