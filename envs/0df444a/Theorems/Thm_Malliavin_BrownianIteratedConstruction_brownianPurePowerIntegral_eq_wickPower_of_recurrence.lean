-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPurePowerIntegral_eq_wickPower_of_recurrence
-- name    : Malliavin.BrownianIteratedConstruction.brownianPurePowerIntegral_eq_wickPower_of_recurrence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:20:00.125004+00:00
-- url     : https://prove2.me/theorems/4d98295f-f606-4699-bd95-1e6223627692
-- title:
--   Brownian Iterated Construction: brownian Pure Power Integral eq wick Power of recurrence
-- statement:
--   The pure-power recurrence and the automatic base orders identify every canonical pure-power
--   integral with its Wick power.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerRecurrence.lean#L99-L109
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerRecurrence.lean#L99-L109

import Definitions.Def_Malliavin_BrownianHermiteMultipleIntegral
import Definitions.Def_Malliavin_BrownianPurePowerRecurrence
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

theorem Malliavin.BrownianIteratedConstruction.brownianPurePowerIntegral_eq_wickPower_of_recurrence
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hrec : BrownianPurePowerHermiteRecurrence hB)
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    brownianPurePowerIntegral hB n (stepToLp v) =
      brownianWickPowerLp hB v n := by sorry
