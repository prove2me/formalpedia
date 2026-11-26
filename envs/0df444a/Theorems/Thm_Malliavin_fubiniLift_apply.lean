-- Prove2me | Theorems.Thm_Malliavin_fubiniLift_apply
-- name    : Malliavin.fubiniLift_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:03:49.473064+00:00
-- url     : https://prove2.me/theorems/c543202d-baf7-52ea-a3ea-dfa6324f21d6
-- title:
--   Malliavin: fubini Lift apply
-- statement:
--   The Malliavin construction uses the fubini Lift apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/FubiniLift.lean#L194-L194
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/FubiniLift.lean#L194-L194

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

theorem Malliavin.fubiniLift_apply (f : Lp (Lp ℝ 2 ν) 2 μ) : fubiniLift f = fubiniLiftL f := by sorry
