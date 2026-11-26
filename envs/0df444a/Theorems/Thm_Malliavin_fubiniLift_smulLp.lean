-- Prove2me | Theorems.Thm_Malliavin_fubiniLift_smulLp
-- name    : Malliavin.fubiniLift_smulLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:51:33.290158+00:00
-- url     : https://prove2.me/theorems/e0298a42-f384-41f4-bca4-ed9f14689b42
-- title:
--   Malliavin: fubini Lift smul Lp
-- statement:
--   **The Fubini lift on rank-one elements**: `fubiniLift (G • g) = g ⊗ G`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/FubiniLift.lean#L326-L346
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/FubiniLift.lean#L326-L346

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Malliavin.fubiniLift_smulLp [SFinite μ] [SFinite ν] (g : Lp ℝ 2 ν) (G : Lp ℝ 2 μ) :
    fubiniLift (smulLp g G) = tensor g G := by sorry
