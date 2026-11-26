-- Prove2me | Theorems.Thm_Malliavin_timeDerivativeEquiv_apply
-- name    : Malliavin.timeDerivativeEquiv_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:29:04.62601+00:00
-- url     : https://prove2.me/theorems/efa4eaec-1948-5995-ac0c-da858236ff8b
-- title:
--   Malliavin: time Derivative Equiv apply
-- statement:
--   The Malliavin construction uses the time Derivative Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L486-L488
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L486-L488

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

theorem Malliavin.timeDerivativeEquiv_apply (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B) (U : Lp (Space P) 2 P) :
    timeDerivativeEquiv hB L hL hgen U = timeDerivative hB L hL hgen U := by sorry
