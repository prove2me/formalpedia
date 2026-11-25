-- Prove2me | Theorems.Thm_Newton_continuous_compactSupport_dense_Lp
-- name    : Newton.continuous_compactSupport_dense_Lp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:30:41.773801+00:00
-- url     : https://prove2.me/theorems/d52e241a-151f-48ad-ba06-559459420be4
-- title:
--   Newton: continuous compact Support dense Lp
-- statement:
--   **Continuous compactly supported functions are dense in Lp.**
--
--   For any f ∈ Lp(ℝⁿ) with 1 ≤ p < ∞ and any ε > 0, there exists
--   a continuous function g with compact support such that ‖f - g‖_p < ε.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/ContinuousDense.lean#L23-L48
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/ContinuousDense.lean#L23-L48

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

theorem Newton.continuous_compactSupport_dense_Lp
    (p : ℝ≥0∞)
    (hp_ne_top : p ≠ ⊤)
    (f : (Fin n → ℝ) → ℂ)
    (hf : MemLp f p (volume : Measure (Fin n → ℝ)))
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : (Fin n → ℝ) → ℂ,
      Continuous g ∧
      HasCompactSupport g ∧
      MemLp g p volume ∧
      eLpNorm (f - g) p volume < ENNReal.ofReal ε := by sorry
