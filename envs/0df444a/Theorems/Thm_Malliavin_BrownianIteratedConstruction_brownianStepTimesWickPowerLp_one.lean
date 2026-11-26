-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianStepTimesWickPowerLp_one
-- name    : Malliavin.BrownianIteratedConstruction.brownianStepTimesWickPowerLp_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:19:38.738857+00:00
-- url     : https://prove2.me/theorems/6f891662-1544-5c76-882e-b1f5ae82e45e
-- title:
--   Brownian Iterated Construction: brownian Step Times Wick Power Lp one
-- statement:
--   At the first recurrence step, multiplication by the step sum gives its raw square.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerRecurrence.lean#L71-L75
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerRecurrence.lean#L71-L75

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

theorem Malliavin.BrownianIteratedConstruction.brownianStepTimesWickPowerLp_one
    (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) :
    brownianStepTimesWickPowerLp hB v 1 = brownianStepPowerLp hB v 2 := by sorry
