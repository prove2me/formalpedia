-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_higherHermiteMultipleIntegralIdentity_iff_fullMixedInner
-- name    : Malliavin.BrownianIteratedConstruction.higherHermiteMultipleIntegralIdentity_iff_fullMixedInner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:20:34.018864+00:00
-- url     : https://prove2.me/theorems/29d25424-f60b-5706-92ac-65fc55dd5849
-- title:
--   Brownian Iterated Construction: higher Hermite Multiple Integral Identity iff full Mixed Inner
-- statement:
--   Including the automatic base orders, the Hermite/multiple-integral identity is exactly the
--   full mixed-inner scalar formula.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickPurePowerComparison.lean#L138-L147
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickPurePowerComparison.lean#L138-L147

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

theorem Malliavin.BrownianIteratedConstruction.higherHermiteMultipleIntegralIdentity_iff_fullMixedInner
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    BrownianHigherHermiteMultipleIntegralIdentity hB ↔
      BrownianWickPurePowerMixedInnerIdentity hB := by sorry
