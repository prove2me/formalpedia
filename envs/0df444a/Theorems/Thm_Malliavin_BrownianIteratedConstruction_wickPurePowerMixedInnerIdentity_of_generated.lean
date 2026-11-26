-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_wickPurePowerMixedInnerIdentity_of_generated
-- name    : Malliavin.BrownianIteratedConstruction.wickPurePowerMixedInnerIdentity_of_generated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:34:44.219865+00:00
-- url     : https://prove2.me/theorems/95745548-94dc-594f-97b4-988533cd9ecd
-- title:
--   Brownian Iterated Construction: wick Pure Power Mixed Inner Identity of generated
-- statement:
--   Generated linear Brownian coordinates satisfy the equivalent all-orders scalar mixed-inner
--   identity.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerDuality.lean#L390-L397
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerDuality.lean#L390-L397

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

theorem Malliavin.BrownianIteratedConstruction.wickPurePowerMixedInnerIdentity_of_generated
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B) (hsm : ∀ t, StronglyMeasurable (B t)) :
    BrownianWickPurePowerMixedInnerIdentity hB := by sorry
