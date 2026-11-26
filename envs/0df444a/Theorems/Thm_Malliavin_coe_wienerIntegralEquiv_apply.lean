-- Prove2me | Theorems.Thm_Malliavin_coe_wienerIntegralEquiv_apply
-- name    : Malliavin.coe_wienerIntegralEquiv_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:12:50.681711+00:00
-- url     : https://prove2.me/theorems/300ae825-3cf6-431c-8c35-b4e74f8c1152
-- title:
--   Malliavin: coe wiener Integral Equiv apply
-- statement:
--   The Malliavin construction uses the coe wiener Integral Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L137-L139
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L137-L139

import Definitions.Def_Malliavin_WienerIntegral
import Definitions.Def_Malliavin_FubiniLift
import Definitions.Def_Malliavin_MalliavinDerivative
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_TimeDerivative
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.coe_wienerIntegralEquiv_apply (hB : IsPreBrownianReal B P)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    (wienerIntegralEquiv hB f : RandomL2 P) = wienerIntegral hB f := by sorry
