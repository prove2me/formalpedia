-- Prove2me | Theorems.Thm_Newton_smooth_cutoff_compactSupport_Lp
-- name    : Newton.smooth_cutoff_compactSupport_Lp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:03:26.025306+00:00
-- url     : https://prove2.me/theorems/b9ad0b07-f2c3-47e7-995b-fde5158fd9c7
-- title:
--   Newton: smooth cutoff compact Support Lp
-- statement:
--   Cutting off a smooth function so that it has compact support while keeping control of the
--   `Lᵖ` error.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/ContinuousDense.lean#L974-L1050
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/ContinuousDense.lean#L974-L1050

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

theorem Newton.smooth_cutoff_compactSupport_Lp
    (p : ℝ≥0∞)
    (hp_one : 1 ≤ p)
    (hp_ne_top : p ≠ ⊤)
    (φ : (Fin n → ℝ) → ℂ)
    (hφ_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) φ)
    (hφ_memLp : MemLp φ p volume)
    {R : ℝ} (hR_pos : 0 < R)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : (Fin n → ℝ) → ℂ,
      ContDiff ℝ (∞ : WithTop ℕ∞) ψ ∧ HasCompactSupport ψ ∧ MemLp ψ p volume ∧
      eLpNorm (fun x => φ x - ψ x) p volume < ENNReal.ofReal ε := by sorry
