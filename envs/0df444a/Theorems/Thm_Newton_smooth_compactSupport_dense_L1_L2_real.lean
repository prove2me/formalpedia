-- Prove2me | Theorems.Thm_Newton_smooth_compactSupport_dense_L1_L2_real
-- name    : Newton.smooth_compactSupport_dense_L1_L2_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:43:11.657691+00:00
-- url     : https://prove2.me/theorems/77a2b4c6-1d8a-49fc-8d19-a465c9afca3d
-- title:
--   Newton: smooth compact Support dense L1 L2 real
-- statement:
--   The Newton construction uses the smooth compact Support dense L1 L2 real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Distribution/SchwartzDensity.lean#L1831-L2033
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Distribution/SchwartzDensity.lean#L1831-L2033

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

theorem Newton.smooth_compactSupport_dense_L1_L2_real
    (f : ℝ → ℂ)
    (hf_L1 : Integrable f volume)
    (hf_L2 : MemLp f 2 volume)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : ℝ → ℂ,
      ContDiff ℝ (∞ : WithTop ℕ∞) g ∧
      HasCompactSupport g ∧
      eLpNorm (f - g) 1 volume < ENNReal.ofReal ε ∧
      eLpNorm (f - g) 2 volume < ENNReal.ofReal ε := by sorry
