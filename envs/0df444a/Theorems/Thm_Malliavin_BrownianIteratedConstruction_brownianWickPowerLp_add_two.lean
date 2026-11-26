-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickPowerLp_add_two
-- name    : Malliavin.BrownianIteratedConstruction.brownianWickPowerLp_add_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:09:25.552887+00:00
-- url     : https://prove2.me/theorems/f1ba3b82-62c7-5cde-9e78-6cc3245d4b85
-- title:
--   Brownian Iterated Construction: brownian Wick Power Lp add two
-- statement:
--   Generalized Brownian Wick powers satisfy the Hermite two-step recurrence in `RandomL2`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerRecurrence.lean#L57-L66
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerRecurrence.lean#L57-L66

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
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.BrownianIteratedConstruction.brownianWickPowerLp_add_two
    (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    brownianWickPowerLp hB v (n + 2) =
      brownianStepTimesWickPowerLp hB v (n + 1) -
        (‖stepToLp v‖ ^ 2 * ((n + 1 : ℕ) : ℝ)) •
          brownianWickPowerLp hB v n := by sorry
