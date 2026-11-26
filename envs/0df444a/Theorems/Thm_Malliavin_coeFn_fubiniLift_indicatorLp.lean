-- Prove2me | Theorems.Thm_Malliavin_coeFn_fubiniLift_indicatorLp
-- name    : Malliavin.coeFn_fubiniLift_indicatorLp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:04:05.240704+00:00
-- url     : https://prove2.me/theorems/cd7fdb7e-ce3a-4541-80d3-40332c19d12a
-- title:
--   Malliavin: coe Fn fubini Lift indicator Lp
-- statement:
--   The Malliavin construction uses the coe Fn fubini Lift indicator Lp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/FubiniLift.lean#L200-L204
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/FubiniLift.lean#L200-L204

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

theorem Malliavin.coeFn_fubiniLift_indicatorLp (A : FiniteMeasurableSet μ) (g : Lp ℝ 2 ν) :
    (fubiniLift (indicatorLp A g) : T × Ω → ℝ) =ᵐ[ν.prod μ]
      fun p ↦ g p.1 * A.1.indicator (1 : Ω → ℝ) p.2 := by sorry
