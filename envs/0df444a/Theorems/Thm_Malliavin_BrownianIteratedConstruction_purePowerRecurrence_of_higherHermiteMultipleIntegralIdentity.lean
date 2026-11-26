-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_purePowerRecurrence_of_higherHermiteMultipleIntegralIdentity
-- name    : Malliavin.BrownianIteratedConstruction.purePowerRecurrence_of_higherHermiteMultipleIntegralIdentity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:12:07.784218+00:00
-- url     : https://prove2.me/theorems/658ab633-6f4b-5b77-abf1-d788dafc5222
-- title:
--   Brownian Iterated Construction: pure Power Recurrence of higher Hermite Multiple Integral Identity
-- statement:
--   Conversely, the higher Hermite/multiple-integral identity forces the matching pure-power
--   recurrence.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerRecurrence.lean#L123-L132
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerRecurrence.lean#L123-L132

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

theorem Malliavin.BrownianIteratedConstruction.purePowerRecurrence_of_higherHermiteMultipleIntegralIdentity
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hid : BrownianHigherHermiteMultipleIntegralIdentity hB) :
    BrownianPurePowerHermiteRecurrence hB := by sorry
