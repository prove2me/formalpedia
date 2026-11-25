-- Prove2me | Theorems.Thm_Newton_phi0_eq_zero_outside_enlarged_ball
-- name    : Newton.phi0_eq_zero_outside_enlarged_ball
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:03:27.950154+00:00
-- url     : https://prove2.me/theorems/9b14d548-41d4-4d5f-b75d-2080608f5dee
-- title:
--   Newton: phi0 eq zero outside enlarged ball
-- statement:
--   The Newton construction uses the phi0 eq zero outside enlarged ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/ContinuousDense.lean#L127-L145
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/ContinuousDense.lean#L127-L145

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

theorem Newton.phi0_eq_zero_outside_enlarged_ball
    (φ₀ : (Fin n → ℝ) → ℂ) (R : ℝ)
    (h_support : tsupport φ₀ ⊆ Metric.closedBall (0 : Fin n → ℝ) (R + 1)) :
    ∀ ⦃x : Fin n → ℝ⦄, R + 1 < ‖x‖ → φ₀ x = 0 := by sorry
