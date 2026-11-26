-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianStepDual_apply
-- name    : Malliavin.BrownianIteratedConstruction.brownianStepDual_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:13:34.027479+00:00
-- url     : https://prove2.me/theorems/1027e428-c622-5031-8251-72c5a2f1d634
-- title:
--   Brownian Iterated Construction: brownian Step Dual apply
-- statement:
--   The Brownian Iterated Construction construction uses the brownian Step Dual apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerDuality.lean#L38-L50
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerDuality.lean#L38-L50

import Definitions.Def_Malliavin_BrownianWickPurePowerComparison
import Definitions.Def_Malliavin_BrownianMultipleIntegralBoxSpan
import Definitions.Def_Malliavin_PastCylinderDensity
import Definitions.Def_Malliavin_BrownianPurePowerDuality
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.BrownianIteratedConstruction.brownianStepDual_apply (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (v : ℝ≥0 →₀ ℝ) (w : W) :
    brownianStepDual coordinate v w = stepSum B v w := by sorry
