-- Prove2me | Theorems.Thm_Newton_cutoff_L1_bound
-- name    : Newton.cutoff_L1_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:52:18.944668+00:00
-- url     : https://prove2.me/theorems/650c3b9e-f74a-4e3b-a374-d5dfebdf9215
-- title:
--   Newton: cutoff L1 bound
-- statement:
--   The Newton construction uses the cutoff L1 bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Distribution/SchwartzDensity.lean#L552-L668
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Distribution/SchwartzDensity.lean#L552-L668

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

theorem Newton.cutoff_L1_bound
    (f : (Fin n → ℝ) → ℂ) (f_cut : (Fin n → ℝ) → ℂ)
    (hf_L1 : MemLp f 1 volume)
    (χ : (Fin n → ℝ) → ℝ)
    (R ε_tail₁ : ℝ)
    (hχ_nonneg : ∀ x, 0 ≤ χ x)
    (hχ_le_one : ∀ x, χ x ≤ 1)
    (hf_cut_def : f_cut = fun x => (χ x : ℂ) * f x)
    (h_diff_zero_inside : ∀ {x : Fin n → ℝ}, ‖x‖ ≤ R → f x - f_cut x = 0)
    (hf_tail_L1 :
      ∫ x, ‖f x‖ ∂(volume.restrict {x : (Fin n → ℝ) | R ≤ ‖x‖}) < ε_tail₁)
    (htail₁ : 0 < ε_tail₁) :
    eLpNorm (fun x => f x - f_cut x) 1 volume ≤ ENNReal.ofReal ε_tail₁ := by sorry
