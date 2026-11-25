-- Prove2me | Theorems.Thm_Newton_triangle_inequality_aux
-- name    : Newton.triangle_inequality_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:15:13.908387+00:00
-- url     : https://prove2.me/theorems/5b2b0702-63a7-42c6-9202-a33c3c7214ec
-- title:
--   Newton: triangle inequality aux
-- statement:
--   The Newton construction uses the triangle inequality aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Distribution/SchwartzDensity.lean#L49-L140
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Distribution/SchwartzDensity.lean#L49-L140

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

theorem Newton.triangle_inequality_aux
    (f g h : (Fin n → ℝ) → ℂ)
    (ε ε₁ ε₂ ε₃ : ℝ)
    (hf_meas : AEStronglyMeasurable f volume)
    (hg_meas : AEStronglyMeasurable g volume)
    (hh_meas : AEStronglyMeasurable h volume)
    (hf : eLpNorm f (1 : ℝ≥0∞) volume < ENNReal.ofReal ε₁)
    (hg : eLpNorm g 1 volume < ENNReal.ofReal ε₂)
    (hh : eLpNorm h 1 volume < ENNReal.ofReal ε₃)
    (h_sum : ε₁ + ε₂ + ε₃ ≤ ε) :
    eLpNorm (fun x => f x + g x + h x) 1 volume < ENNReal.ofReal ε := by sorry
