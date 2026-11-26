-- Prove2me | Theorems.Thm_Malliavin_inner_fubiniLift_tensorLp
-- name    : Malliavin.inner_fubiniLift_tensorLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:54:11.369988+00:00
-- url     : https://prove2.me/theorems/a89bfd84-668c-45dd-8465-0b27d8a5dd6e
-- title:
--   Malliavin: inner fubini Lift tensor Lp
-- statement:
--   **Weak Fubini identity**: pairing the lift of `U` with a simple tensor `g ⊗ 1_A` is the
--   integral over `A` of the `L²(ν)` pairing `⟪g, U ω⟫`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/FubiniLift.lean#L208-L212
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/FubiniLift.lean#L208-L212

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

theorem Malliavin.inner_fubiniLift_tensorLp (U : Lp (Lp ℝ 2 ν) 2 μ) (A : FiniteMeasurableSet μ)
    (g : Lp ℝ 2 ν) :
    ⟪fubiniLift U, tensorLp A g⟫_ℝ = ∫ ω in A.1, ⟪g, U ω⟫_ℝ ∂μ := by sorry
