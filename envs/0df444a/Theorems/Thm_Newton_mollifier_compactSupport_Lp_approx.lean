-- Prove2me | Theorems.Thm_Newton_mollifier_compactSupport_Lp_approx
-- name    : Newton.mollifier_compactSupport_Lp_approx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:03:18.355919+00:00
-- url     : https://prove2.me/theorems/3ec31525-47ca-4fb3-bdc9-87d20f09c979
-- title:
--   Newton: mollifier compact Support Lp approx
-- statement:
--   Approximating a continuous compactly supported function by a smooth function in `Lᵖ`.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/ContinuousDense.lean#L148-L762
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/ContinuousDense.lean#L148-L762

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

theorem Newton.mollifier_compactSupport_Lp_approx
    (p : ℝ≥0∞) (hp_one : 1 ≤ p) (g : (Fin n → ℝ) → ℂ)
    (hg_cont : Continuous g) (hg_compact : HasCompactSupport g) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : (Fin n → ℝ) → ℂ,
      ContDiff ℝ (∞ : WithTop ℕ∞) φ ∧
      eLpNorm (fun x => g x - φ x) p volume < ENNReal.ofReal ε ∧
      MemLp φ p volume := by sorry
