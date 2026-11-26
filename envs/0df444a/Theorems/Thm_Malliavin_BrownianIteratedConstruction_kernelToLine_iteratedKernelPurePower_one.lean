-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_kernelToLine_iteratedKernelPurePower_one
-- name    : Malliavin.BrownianIteratedConstruction.kernelToLine_iteratedKernelPurePower_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:18:03.559052+00:00
-- url     : https://prove2.me/theorems/b9acf61f-2a55-4b7b-903d-dffc18f2a50c
-- title:
--   Brownian Iterated Construction: kernel To Line iterated Kernel Pure Power one
-- statement:
--   Under the order-one kernel equivalence, a pure power is its original time kernel.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerIntegral.lean#L126-L140
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerIntegral.lean#L126-L140

import Definitions.Def_Malliavin_IteratedKernelPurePower
import Definitions.Def_Malliavin_BrownianPolynomialHermite
import Definitions.Def_Malliavin_BrownianPurePowerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.BrownianIteratedConstruction.kernelToLine_iteratedKernelPurePower_one
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    kernelToLine (iteratedKernelPurePower 1 f) = f := by sorry
