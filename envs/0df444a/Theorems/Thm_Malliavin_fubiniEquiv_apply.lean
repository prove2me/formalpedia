-- Prove2me | Theorems.Thm_Malliavin_fubiniEquiv_apply
-- name    : Malliavin.fubiniEquiv_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:04:22.687843+00:00
-- url     : https://prove2.me/theorems/15a1f959-0f52-503c-a885-a6522091b642
-- title:
--   Malliavin: fubini Equiv apply
-- statement:
--   The Malliavin construction uses the fubini Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/FubiniLift.lean#L665-L665
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/FubiniLift.lean#L665-L665

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_FubiniLift
set_option autoImplicit false
open MeasureTheory Filter Topology Function
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3
open Malliavin
variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] {μ : Measure Ω} {ν : Measure T}
variable [SFinite μ] [SFinite ν]
variable [SigmaFinite μ] [SigmaFinite ν]

theorem Malliavin.fubiniEquiv_apply (f : Lp (Lp ℝ 2 ν) 2 μ) : fubiniEquiv f = fubiniLift f := by sorry
