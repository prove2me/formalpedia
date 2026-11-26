-- Prove2me | Theorems.Thm_Malliavin_timeDerivativeOfFirstChaos_apply
-- name    : Malliavin.timeDerivativeOfFirstChaos_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:11:17.896709+00:00
-- url     : https://prove2.me/theorems/35e4d78f-24b7-5076-abe2-b68df320026b
-- title:
--   Malliavin: time Derivative Of First Chaos apply
-- statement:
--   The Malliavin construction uses the time Derivative Of First Chaos apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L178-L181
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L178-L181

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

theorem Malliavin.timeDerivativeOfFirstChaos_apply (hB : IsPreBrownianReal B P)
    (U : Lp (firstChaos hB) 2 P) :
    timeDerivativeOfFirstChaos hB U =
      fubiniLift (compLpₗᵢ (wienerIntegralEquiv hB).symm.toLinearIsometry U) := by sorry
