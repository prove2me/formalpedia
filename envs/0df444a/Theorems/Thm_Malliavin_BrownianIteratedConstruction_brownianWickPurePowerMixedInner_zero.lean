-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickPurePowerMixedInner_zero
-- name    : Malliavin.BrownianIteratedConstruction.brownianWickPurePowerMixedInner_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:19:52.299055+00:00
-- url     : https://prove2.me/theorems/b562070b-6130-5ae5-b245-507e733ec0de
-- title:
--   Brownian Iterated Construction: brownian Wick Pure Power Mixed Inner zero
-- statement:
--   The mixed-inner formula is automatic at order zero.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickPurePowerComparison.lean#L70-L77
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickPurePowerComparison.lean#L70-L77

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
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.BrownianIteratedConstruction.brownianWickPurePowerMixedInner_zero
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (v : ℝ≥0 →₀ ℝ) :
    inner ℝ (brownianWickPowerLp hB v 0)
      (brownianPurePowerIntegral hB 0 (stepToLp v)) =
      (Nat.factorial 0 : ℝ) * (‖stepToLp v‖ ^ 2) ^ 0 := by sorry
