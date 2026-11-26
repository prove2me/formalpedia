-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_higherHermiteMultipleIntegralIdentity_iff_mixedInner
-- name    : Malliavin.BrownianIteratedConstruction.higherHermiteMultipleIntegralIdentity_iff_mixedInner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:13:37.021853+00:00
-- url     : https://prove2.me/theorems/16de5a6a-71b7-46ed-b05a-942399aa6dec
-- title:
--   Brownian Iterated Construction: higher Hermite Multiple Integral Identity iff mixed Inner
-- statement:
--   The higher Hermite/multiple-integral identity is exactly its mixed-inner scalar formula.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickPurePowerComparison.lean#L124-L134
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickPurePowerComparison.lean#L124-L134

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

theorem Malliavin.BrownianIteratedConstruction.higherHermiteMultipleIntegralIdentity_iff_mixedInner
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    BrownianHigherHermiteMultipleIntegralIdentity hB ↔
      BrownianHigherWickPurePowerMixedInnerIdentity hB := by sorry
