-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPurePowerIntegral_zero_step
-- name    : Malliavin.BrownianIteratedConstruction.brownianPurePowerIntegral_zero_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:07:46.649995+00:00
-- url     : https://prove2.me/theorems/e1e5e11e-7fc8-5f9b-ae5d-08c585d77fa9
-- title:
--   Brownian Iterated Construction: brownian Pure Power Integral zero step
-- statement:
--   At order zero the pure-power multiple integral agrees with the concrete Wick power.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerIntegral.lean#L161-L164
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerIntegral.lean#L161-L164

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

theorem Malliavin.BrownianIteratedConstruction.brownianPurePowerIntegral_zero_step
    (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) :
    brownianPurePowerIntegral hB 0 (stepToLp v) = brownianWickPowerLp hB v 0 := by sorry
