-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickPurePowerMixedInner_one
-- name    : Malliavin.BrownianIteratedConstruction.brownianWickPurePowerMixedInner_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:20:05.177682+00:00
-- url     : https://prove2.me/theorems/e918dee6-db17-5944-b059-8866db0de679
-- title:
--   Brownian Iterated Construction: brownian Wick Pure Power Mixed Inner one
-- statement:
--   The mixed-inner formula is automatic at order one.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickPurePowerComparison.lean#L80-L87
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickPurePowerComparison.lean#L80-L87

import Definitions.Def_Malliavin_BrownianWickIsometry
import Definitions.Def_Malliavin_BrownianPurePowerRecurrence
import Definitions.Def_Malliavin_BrownianWickPurePowerComparison
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

theorem Malliavin.BrownianIteratedConstruction.brownianWickPurePowerMixedInner_one
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (v : ℝ≥0 →₀ ℝ) :
    inner ℝ (brownianWickPowerLp hB v 1)
      (brownianPurePowerIntegral hB 1 (stepToLp v)) =
      (Nat.factorial 1 : ℝ) * (‖stepToLp v‖ ^ 2) ^ 1 := by sorry
