-- Prove2me | Theorems.Thm_Newton_smooth_compactSupport_to_schwartz
-- name    : Newton.smooth_compactSupport_to_schwartz
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:03:24.591543+00:00
-- url     : https://prove2.me/theorems/9ea138e2-9251-4ad8-9014-9c97b4371093
-- title:
--   Newton: smooth compact Support to schwartz
-- statement:
--   Smooth compactly supported functions are Schwartz.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/ContinuousDense.lean#L1053-L1105
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/ContinuousDense.lean#L1053-L1105

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

theorem Newton.smooth_compactSupport_to_schwartz
    (g : (Fin n → ℝ) → ℂ)
    (hg_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) g)
    (hg_support : HasCompactSupport g) :
    ∃ φ : 𝓢((Fin n → ℝ), ℂ), (φ : (Fin n → ℝ) → ℂ) = g := by sorry
