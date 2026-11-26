-- Prove2me | Theorems.Thm_Malliavin_timeDerivativeOfFirstChaos_indicatorConstLp
-- name    : Malliavin.timeDerivativeOfFirstChaos_indicatorConstLp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:28:50.487749+00:00
-- url     : https://prove2.me/theorems/6bfbd5f1-4903-4821-9ab4-b460a6162041
-- title:
--   Malliavin: time Derivative Of First Chaos indicator Const Lp
-- statement:
--   On a simple tensor `1_A • J₁ g` the time derivative is `(t, ω) ↦ g t · 1_A ω`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L184-L190
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L184-L190

import Definitions.Def_Malliavin_WienerIntegral
import Definitions.Def_Malliavin_FubiniLift
import Definitions.Def_Malliavin_MalliavinDerivative
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_TimeDerivative
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} [SFinite P]

theorem Malliavin.timeDerivativeOfFirstChaos_indicatorConstLp (hB : IsPreBrownianReal B P)
    (A : FiniteMeasurableSet P) (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    timeDerivativeOfFirstChaos hB (indicatorConstLp 2 A.2.1 A.2.2 (wienerIntegralEquiv hB g)) =
      tensorLp A g := by sorry
