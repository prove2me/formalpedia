-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPurePowerIntegral_one_step
-- name    : Malliavin.BrownianIteratedConstruction.brownianPurePowerIntegral_one_step
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:08:34.724394+00:00
-- url     : https://prove2.me/theorems/94a82ce6-cd21-5202-b3f0-ff59fa9ff85a
-- title:
--   Brownian Iterated Construction: brownian Pure Power Integral one step
-- statement:
--   The genuine first multiple integral of a Brownian step kernel is its first Wick power.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerIntegral.lean#L167-L174
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerIntegral.lean#L167-L174

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

theorem Malliavin.BrownianIteratedConstruction.brownianPurePowerIntegral_one_step
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (v : ℝ≥0 →₀ ℝ) :
    brownianPurePowerIntegral hB 1 (stepToLp v) = brownianWickPowerLp hB v 1 := by sorry
