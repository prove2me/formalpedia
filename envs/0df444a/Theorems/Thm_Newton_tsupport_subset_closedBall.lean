-- Prove2me | Theorems.Thm_Newton_tsupport_subset_closedBall
-- name    : Newton.tsupport_subset_closedBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:30:42.843651+00:00
-- url     : https://prove2.me/theorems/ef43bb69-12c3-4d89-96d2-fb02b99d2772
-- title:
--   Newton: tsupport subset closed Ball
-- statement:
--   Any compactly supported function has its topological support
--       contained in some closed ball of radius at least 1.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/ContinuousDense.lean#L52-L63
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/ContinuousDense.lean#L52-L63

import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_ContinuousDense
set_option autoImplicit false
open MeasureTheory NNReal SchwartzMap
open scoped ENNReal ContDiff Topology
open Newton
variable {n : ℕ}

theorem Newton.tsupport_subset_closedBall
    (g : (Fin n → ℝ) → ℂ) (hg_compact : HasCompactSupport g) :
    ∃ R : ℝ, tsupport g ⊆ Metric.closedBall (0 : Fin n → ℝ) R ∧ 1 ≤ R := by sorry
