-- Prove2me | Theorems.Thm_Newton_smooth_cutoff_compactSupport_Lp_aux
-- name    : Newton.smooth_cutoff_compactSupport_Lp_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:03:28.407007+00:00
-- url     : https://prove2.me/theorems/bc61b04e-8e99-496c-ae2c-75b0a0bfaad9
-- title:
--   Newton: smooth cutoff compact Support Lp aux
-- statement:
--   Auxiliary lemma: smoothly cut off a continuous compactly supported function while
--   keeping control of the `Lᵖ` error.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/ContinuousDense.lean#L766-L970
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/ContinuousDense.lean#L766-L970

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

theorem Newton.smooth_cutoff_compactSupport_Lp_aux
    (p : ℝ≥0∞) (hp_one : 1 ≤ p)
    (g : (Fin n → ℝ) → ℂ)
    (hg_cont : Continuous g)
    (hg_compact : HasCompactSupport g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : (Fin n → ℝ) → ℂ,
      ContDiff ℝ (∞ : WithTop ℕ∞) ψ ∧
      HasCompactSupport ψ ∧
      MemLp ψ p volume ∧
      eLpNorm (fun x => g x - ψ x) p volume < ENNReal.ofReal ε := by sorry
