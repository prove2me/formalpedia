-- Prove2me | Theorems.Thm_Malliavin_norm_timeDerivativeOfEq
-- name    : Malliavin.norm_timeDerivativeOfEq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:29:00.67107+00:00
-- url     : https://prove2.me/theorems/22b3cd4f-dcd8-4b9f-86e3-9637a11f010b
-- title:
--   Malliavin: norm time Derivative Of Eq
-- statement:
--   The Malliavin construction uses the norm time Derivative Of Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L251-L253
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L251-L253

import Definitions.Def_Malliavin_WienerIntegral
import Definitions.Def_Malliavin_FubiniLift
import Definitions.Def_Malliavin_MalliavinDerivative
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_TimeDerivative
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W]

theorem Malliavin.norm_timeDerivativeOfEq (hB : IsPreBrownianReal B P) (hS : Space P = firstChaos hB)
    (U : Lp (Space P) 2 P) : ‖timeDerivativeOfEq hB hS U‖ = ‖U‖ := by sorry
