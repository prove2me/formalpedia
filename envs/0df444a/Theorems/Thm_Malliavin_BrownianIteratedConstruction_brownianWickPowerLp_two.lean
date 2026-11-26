-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickPowerLp_two
-- name    : Malliavin.BrownianIteratedConstruction.brownianWickPowerLp_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:31:17.907853+00:00
-- url     : https://prove2.me/theorems/313aa60e-59aa-5412-8a81-0af6d38c4f6b
-- title:
--   Brownian Iterated Construction: brownian Wick Power Lp two
-- statement:
--   The second Wick power is the raw square minus its variance.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerRecurrence.lean#L79-L86
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerRecurrence.lean#L79-L86

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
omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W]

theorem Malliavin.BrownianIteratedConstruction.brownianWickPowerLp_two
    (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) :
    brownianWickPowerLp hB v 2 =
      brownianStepPowerLp hB v 2 -
        ‖stepToLp v‖ ^ 2 • Lp.const 2 P (1 : ℝ) := by sorry
