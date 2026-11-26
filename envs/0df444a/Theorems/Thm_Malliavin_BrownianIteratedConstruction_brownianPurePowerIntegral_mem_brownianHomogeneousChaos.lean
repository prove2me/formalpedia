-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPurePowerIntegral_mem_brownianHomogeneousChaos
-- name    : Malliavin.BrownianIteratedConstruction.brownianPurePowerIntegral_mem_brownianHomogeneousChaos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:09:29.781396+00:00
-- url     : https://prove2.me/theorems/e998092d-92a8-5fab-86e9-97267576ab2d
-- title:
--   Brownian Iterated Construction: brownian Pure Power Integral mem brownian Homogeneous Chaos
-- statement:
--   A pure-power multiple integral belongs to its canonical Brownian homogeneous chaos.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerIntegral.lean#L50-L56
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerIntegral.lean#L50-L56

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
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.BrownianIteratedConstruction.brownianPurePowerIntegral_mem_brownianHomogeneousChaos
    (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    brownianPurePowerIntegral hB n f ∈ brownianHomogeneousChaos hB n := by sorry
