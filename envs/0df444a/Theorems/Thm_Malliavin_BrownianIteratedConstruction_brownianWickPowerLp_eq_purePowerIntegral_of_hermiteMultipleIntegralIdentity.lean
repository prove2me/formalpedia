-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickPowerLp_eq_purePowerIntegral_of_hermiteMultipleIntegralIdentity
-- name    : Malliavin.BrownianIteratedConstruction.brownianWickPowerLp_eq_purePowerIntegral_of_hermiteMultipleIntegralIdentity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:19:10.792008+00:00
-- url     : https://prove2.me/theorems/a53ae083-957c-4aed-bcde-f97de8aee7df
-- title:
--   Brownian Iterated Construction: brownian Wick Power Lp eq pure Power Integral of hermite Multiple Integral Identity
-- statement:
--   The higher-order identity, together with the automatic base orders, identifies every Wick
--   power with its canonical pure-power multiple integral.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermiteMultipleIntegral.lean#L41-L52
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermiteMultipleIntegral.lean#L41-L52

import Definitions.Def_Malliavin_BrownianPurePowerIntegral
import Definitions.Def_Malliavin_BrownianHermiteMultipleIntegral
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

theorem Malliavin.BrownianIteratedConstruction.brownianWickPowerLp_eq_purePowerIntegral_of_hermiteMultipleIntegralIdentity
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hid : BrownianHigherHermiteMultipleIntegralIdentity hB)
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    brownianWickPowerLp hB v n =
      brownianPurePowerIntegral hB n (stepToLp v) := by sorry
