-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_purePowerRecurrence_iff_higherHermiteMultipleIntegralIdentity
-- name    : Malliavin.BrownianIteratedConstruction.purePowerRecurrence_iff_higherHermiteMultipleIntegralIdentity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:19:52.539863+00:00
-- url     : https://prove2.me/theorems/2932d5dd-b59d-5b1d-856c-4a921425357f
-- title:
--   Brownian Iterated Construction: pure Power Recurrence iff higher Hermite Multiple Integral Identity
-- statement:
--   The all-order identity is exactly the pure-power Itô product recurrence.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerRecurrence.lean#L135-L140
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerRecurrence.lean#L135-L140

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

theorem Malliavin.BrownianIteratedConstruction.purePowerRecurrence_iff_higherHermiteMultipleIntegralIdentity
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    BrownianPurePowerHermiteRecurrence hB ↔
      BrownianHigherHermiteMultipleIntegralIdentity hB := by sorry
