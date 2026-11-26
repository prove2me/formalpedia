-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_wickPurePowerMixedInnerIdentity_iff_higher
-- name    : Malliavin.BrownianIteratedConstruction.wickPurePowerMixedInnerIdentity_iff_higher
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:12:13.683322+00:00
-- url     : https://prove2.me/theorems/1854eb2d-306b-57ae-9fea-8e7792247091
-- title:
--   Brownian Iterated Construction: wick Pure Power Mixed Inner Identity iff higher
-- statement:
--   Since the mixed-inner formula is automatic in orders zero and one, its all-orders and
--   genuinely higher-order forms are equivalent.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickPurePowerComparison.lean#L107-L120
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickPurePowerComparison.lean#L107-L120

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

theorem Malliavin.BrownianIteratedConstruction.wickPurePowerMixedInnerIdentity_iff_higher
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    BrownianWickPurePowerMixedInnerIdentity hB ↔
      BrownianHigherWickPurePowerMixedInnerIdentity hB := by sorry
