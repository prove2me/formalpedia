-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianMultipleIntegralCLM_one_eq_wienerIntegralKernel
-- name    : Malliavin.BrownianIteratedConstruction.brownianMultipleIntegralCLM_one_eq_wienerIntegralKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:15:11.372151+00:00
-- url     : https://prove2.me/theorems/88e588b4-66b6-45bf-985a-e21a3bedaf26
-- title:
--   Brownian Iterated Construction: brownian Multiple Integral CLM one eq wiener Integral Kernel
-- statement:
--   At order one the canonical Brownian multiple operator is the genuine Wiener integral.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegral.lean#L171-L186
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegral.lean#L171-L186

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

theorem Malliavin.BrownianIteratedConstruction.brownianMultipleIntegralCLM_one_eq_wienerIntegralKernel
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    brownianMultipleIntegralCLM hB 1 = wienerIntegralKernel hB := by sorry
