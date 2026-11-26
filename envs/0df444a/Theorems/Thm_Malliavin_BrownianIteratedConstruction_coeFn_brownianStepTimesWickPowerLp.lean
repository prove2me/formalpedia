-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_coeFn_brownianStepTimesWickPowerLp
-- name    : Malliavin.BrownianIteratedConstruction.coeFn_brownianStepTimesWickPowerLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:31:35.605061+00:00
-- url     : https://prove2.me/theorems/210c5b80-30f1-4e27-8dc5-8536c144d498
-- title:
--   Brownian Iterated Construction: coe Fn brownian Step Times Wick Power Lp
-- statement:
--   The recurrence's leading term has the intended pointwise product representative.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerRecurrence.lean#L41-L52
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerRecurrence.lean#L41-L52

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

theorem Malliavin.BrownianIteratedConstruction.coeFn_brownianStepTimesWickPowerLp
    (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    (brownianStepTimesWickPowerLp hB v n : W → ℝ) =ᵐ[P]
      fun w ↦ stepSum B v w *
        (varianceHermite (‖stepToLp v‖ ^ 2) n).eval (stepSum B v w) := by sorry
