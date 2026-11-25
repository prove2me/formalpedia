-- Prove2me | Theorems.Thm_Newton_eLpNorm_triangle_ineq_lt
-- name    : Newton.eLpNorm_triangle_ineq_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:03:13.710357+00:00
-- url     : https://prove2.me/theorems/645d2d58-41b6-42da-9f66-9d4bce7717eb
-- title:
--   Newton: e Lp Norm triangle ineq lt
-- statement:
--   The Newton construction uses the e Lp Norm triangle ineq lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/ContinuousDense.lean#L74-L125
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/ContinuousDense.lean#L74-L125

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

theorem Newton.eLpNorm_triangle_ineq_lt
    {g φ₀ ψ : (Fin n → ℝ) → ℂ}
    (p : ℝ≥0∞)
    (hp_one : 1 ≤ p)
    (hg_cont : Continuous g)
    (hφ₀_smooth : ContDiff ℝ ∞ φ₀)
    (hψ_cont : Continuous ψ)
    {ε : ℝ}
    (h_term_support : eLpNorm (fun x => g x - φ₀ x) p volume < ENNReal.ofReal (ε / 2))
    (h_term_cutoff : eLpNorm (fun x => φ₀ x - ψ x) p volume < ENNReal.ofReal (ε / 2))
    (hε_half : 0 < ε / 2) :
    eLpNorm (fun x => g x - ψ x) p volume < ENNReal.ofReal ε := by sorry
