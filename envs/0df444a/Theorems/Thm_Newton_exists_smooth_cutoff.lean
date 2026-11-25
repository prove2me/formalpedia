-- Prove2me | Theorems.Thm_Newton_exists_smooth_cutoff
-- name    : Newton.exists_smooth_cutoff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:52:16.350403+00:00
-- url     : https://prove2.me/theorems/206d25a9-ff99-4735-895a-86e5ba1ddf63
-- title:
--   Newton: exists smooth cutoff
-- statement:
--   The Newton construction uses the exists smooth cutoff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Distribution/SchwartzDensity.lean#L20-L47
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Distribution/SchwartzDensity.lean#L20-L47

import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_Newton_Analysis_Convolution_ApproximateIdentity
import Definitions.Def_Newton_Analysis_Convolution_Bounds
import Definitions.Def_Newton_Analysis_Distribution_SchwartzDensity
set_option autoImplicit false
open MeasureTheory SchwartzMap Complex NNReal
open scoped ENNReal ContDiff Topology Convolution ComplexConjugate
open Newton
variable {n : ℕ}

theorem Newton.exists_smooth_cutoff
    (r R : ℝ) (hr : 0 < r) (hR : r < R) :
    ∃ χ : (Fin n → ℝ) → ℝ,
      ContDiff ℝ (∞ : WithTop ℕ∞) χ ∧
      (∀ x, ‖x‖ ≤ r → χ x = 1) ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      HasCompactSupport χ ∧
      tsupport χ ⊆ Metric.closedBall (0 : Fin n → ℝ) R := by sorry
