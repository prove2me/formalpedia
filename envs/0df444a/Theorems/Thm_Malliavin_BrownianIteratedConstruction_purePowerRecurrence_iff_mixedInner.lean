-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_purePowerRecurrence_iff_mixedInner
-- name    : Malliavin.BrownianIteratedConstruction.purePowerRecurrence_iff_mixedInner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:22:04.743401+00:00
-- url     : https://prove2.me/theorems/d37045f8-55fd-4514-b9f0-09d7bcea002f
-- title:
--   Brownian Iterated Construction: pure Power Recurrence iff mixed Inner
-- statement:
--   Equivalently, the pure-power Itô recurrence is exactly the higher mixed-inner formula.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickPurePowerComparison.lean#L150-L155
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickPurePowerComparison.lean#L150-L155

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

theorem Malliavin.BrownianIteratedConstruction.purePowerRecurrence_iff_mixedInner
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    BrownianPurePowerHermiteRecurrence hB ↔
      BrownianHigherWickPurePowerMixedInnerIdentity hB := by sorry
