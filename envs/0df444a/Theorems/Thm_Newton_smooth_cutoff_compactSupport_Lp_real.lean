-- Prove2me | Theorems.Thm_Newton_smooth_cutoff_compactSupport_Lp_real
-- name    : Newton.smooth_cutoff_compactSupport_Lp_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:42:19.776652+00:00
-- url     : https://prove2.me/theorems/d5f76414-bb10-4543-91d4-a751635bc877
-- title:
--   Newton: smooth cutoff compact Support Lp real
-- statement:
--   **Variant for ℝ (n=1 case) with simultaneous L¹ and L² control.**
--
--   This is the specific instance needed for the Plancherel theorem on ℝ.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Distribution/SchwartzDensity.lean#L1441-L1537
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Distribution/SchwartzDensity.lean#L1441-L1537

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

theorem Newton.smooth_cutoff_compactSupport_Lp_real
    (φ : ℝ → ℂ)
    (hφ_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) φ)
    (hφ_memLp : MemLp φ (2 : ℝ≥0∞) volume)
    {R : ℝ} (hR_pos : 0 < R)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℂ,
      ContDiff ℝ (∞ : WithTop ℕ∞) g ∧
      HasCompactSupport g ∧
      MemLp g (2 : ℝ≥0∞) volume ∧
      eLpNorm (fun t => φ t - g t) (2 : ℝ≥0∞) volume < ENNReal.ofReal ε := by sorry
