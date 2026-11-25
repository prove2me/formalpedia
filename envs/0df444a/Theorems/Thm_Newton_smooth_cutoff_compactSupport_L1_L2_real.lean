-- Prove2me | Theorems.Thm_Newton_smooth_cutoff_compactSupport_L1_L2_real
-- name    : Newton.smooth_cutoff_compactSupport_L1_L2_real
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:16:49.371542+00:00
-- url     : https://prove2.me/theorems/e2e0bd30-bfb9-4212-9eb9-3af9461837cd
-- title:
--   Newton: smooth cutoff compact Support L1 L2 real
-- statement:
--   The Newton construction uses the smooth cutoff compact Support L1 L2 real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Distribution/SchwartzDensity.lean#L1539-L1829
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Distribution/SchwartzDensity.lean#L1539-L1829

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

theorem Newton.smooth_cutoff_compactSupport_L1_L2_real
    (φ : ℝ → ℂ)
    (hφ_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) φ)
    (hφ_memLp₁ : MemLp φ 1 volume)
    (hφ_memLp₂ : MemLp φ 2 volume)
    {R : ℝ} (hR_pos : 0 < R)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℂ,
      ContDiff ℝ (∞ : WithTop ℕ∞) g ∧
      HasCompactSupport g ∧
      MemLp g 2 volume ∧
      eLpNorm (fun t => φ t - g t) 1 volume < ENNReal.ofReal ε ∧
      eLpNorm (fun t => φ t - g t) 2 volume < ENNReal.ofReal ε := by sorry
