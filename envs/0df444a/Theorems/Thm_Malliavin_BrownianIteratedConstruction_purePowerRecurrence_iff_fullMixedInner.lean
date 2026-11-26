-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_purePowerRecurrence_iff_fullMixedInner
-- name    : Malliavin.BrownianIteratedConstruction.purePowerRecurrence_iff_fullMixedInner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:34:02.968996+00:00
-- url     : https://prove2.me/theorems/e8a3005a-cdd1-445e-b905-b0cf013f66fd
-- title:
--   Brownian Iterated Construction: pure Power Recurrence iff full Mixed Inner
-- statement:
--   Equivalently, the pure-power Itô recurrence is exactly the full mixed-inner scalar
--   formula, whose base orders hold automatically.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickPurePowerComparison.lean#L159-L168
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickPurePowerComparison.lean#L159-L168

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

theorem Malliavin.BrownianIteratedConstruction.purePowerRecurrence_iff_fullMixedInner
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    BrownianPurePowerHermiteRecurrence hB ↔
      BrownianWickPurePowerMixedInnerIdentity hB := by sorry
