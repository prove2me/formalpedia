-- Prove2me | Theorems.Thm_Newton_cutoff_L2_bound
-- name    : Newton.cutoff_L2_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:52:12.52986+00:00
-- url     : https://prove2.me/theorems/da864510-436f-45e5-8251-6382f944e1d2
-- title:
--   Newton: cutoff L2 bound
-- statement:
--   The Newton construction uses the cutoff L2 bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Distribution/SchwartzDensity.lean#L670-L804
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Distribution/SchwartzDensity.lean#L670-L804

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

theorem Newton.cutoff_L2_bound
    (f : (Fin n → ℝ) → ℂ) (f_cut : (Fin n → ℝ) → ℂ)
    (χ : (Fin n → ℝ) → ℝ)
    (R ε_tail₂ : ℝ)
    (hχ_nonneg : ∀ x, 0 ≤ χ x)
    (hχ_le_one : ∀ x, χ x ≤ 1)
    (hf_cut_def : f_cut = fun x => (χ x : ℂ) * f x)
    (h_diff_zero_inside : ∀ {x : Fin n → ℝ}, ‖x‖ ≤ R → f x - f_cut x = 0)
    (hf_tail_L2 :
      eLpNorm (fun x => f x) 2 (volume.restrict {x : (Fin n → ℝ) | R ≤ ‖x‖})
        < ENNReal.ofReal ε_tail₂) :
    eLpNorm (fun x => f x - f_cut x) 2 volume ≤ ENNReal.ofReal ε_tail₂ := by sorry
