-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPurePowerIntegral_zero
-- name    : Malliavin.BrownianIteratedConstruction.brownianPurePowerIntegral_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:17:55.074984+00:00
-- url     : https://prove2.me/theorems/14099996-68a2-5082-aa24-184a311c319f
-- title:
--   Brownian Iterated Construction: brownian Pure Power Integral zero
-- statement:
--   The genuine zeroth multiple integral of any pure power is the constant one.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerIntegral.lean#L144-L157
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerIntegral.lean#L144-L157

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
omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W]

theorem Malliavin.BrownianIteratedConstruction.brownianPurePowerIntegral_zero
    (hB : IsPreBrownianReal B P) (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    brownianPurePowerIntegral hB 0 f = Lp.const 2 P (1 : ℝ) := by sorry
