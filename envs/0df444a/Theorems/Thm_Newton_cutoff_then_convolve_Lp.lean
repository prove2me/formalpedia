-- Prove2me | Theorems.Thm_Newton_cutoff_then_convolve_Lp
-- name    : Newton.cutoff_then_convolve_Lp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:16:45.187023+00:00
-- url     : https://prove2.me/theorems/a407b136-f799-407b-883a-f7a43392e648
-- title:
--   Newton: cutoff then convolve Lp
-- statement:
--   The Newton construction uses the cutoff then convolve Lp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Distribution/SchwartzDensity.lean#L806-L1292
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Distribution/SchwartzDensity.lean#L806-L1292

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

theorem Newton.cutoff_then_convolve_Lp
    (f : (Fin n → ℝ) → ℂ)
    (hf_L1 : MemLp f 1 volume)
    (hf_L2 : MemLp f 2 volume)
    (R : ℝ) (hR : 0 < R)
    {ε ε_cut₁ ε_cut₂ ε_tail₁ ε_tail₂ : ℝ}
    (hε : 0 < ε)
    (hcut₁ : 0 < ε_cut₁) (hcut₂ : 0 < ε_cut₂)
    (htail₁ : 0 < ε_tail₁) (htail₂ : 0 < ε_tail₂)
    (h_budget_L1 : ε_cut₁ + ε_tail₁ < ε)
    (h_budget_L2 : ε_cut₂ + ε_tail₂ < ε)
    (hf_tail_L1 :
      ∫ x, ‖f x‖ ∂(volume.restrict {x : (Fin n → ℝ) | R ≤ ‖x‖}) < ε_tail₁)
    (hf_tail_L2 :
      eLpNorm (fun x => f x) 2 (volume.restrict {x : (Fin n → ℝ) | R ≤ ‖x‖})
        < ENNReal.ofReal ε_tail₂) :
    ∃ φ : 𝓢((Fin n → ℝ), ℂ),
      tsupport (φ : (Fin n → ℝ) → ℂ) ⊆ Metric.closedBall (0 : Fin n → ℝ) (R + 3) ∧
      eLpNorm (fun x => f x - φ x) 1 volume < ENNReal.ofReal ε ∧
      eLpNorm (fun x => f x - φ x) 2 volume < ENNReal.ofReal ε := by sorry
