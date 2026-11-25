-- Prove2me | Theorems.Thm_Newton_exists_mollifier_scale
-- name    : Newton.exists_mollifier_scale
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:15:24.526259+00:00
-- url     : https://prove2.me/theorems/37b37256-e591-4a83-a1c1-c68347f316b4
-- title:
--   Newton: exists mollifier scale
-- statement:
--   The Newton construction uses the exists mollifier scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Distribution/SchwartzDensity.lean#L142-L550
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Distribution/SchwartzDensity.lean#L142-L550

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

theorem Newton.exists_mollifier_scale
    (f₀ : (Fin n → ℝ) → ℂ)
    (hf₀_L1 : MemLp f₀ 1 volume)
    (hf₀_L2 : MemLp f₀ 2 volume)
    (ε₁ ε₂ : ℝ) (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) :
    ∃ (η : ℝ) (_ : 0 < η) (_ : η ≤ 1) (ψ : (Fin n → ℝ) → ℝ),
      ContDiff ℝ (∞ : WithTop ℕ∞) ψ ∧
      HasCompactSupport ψ ∧
      (∫ x, ψ x = 1) ∧
      (∀ x, 0 ≤ ψ x) ∧
      tsupport ψ ⊆ Metric.closedBall (0 : Fin n → ℝ) 1 ∧
      (let ψ_η := fun x => η^(-(n : ℝ)) * ψ (fun i => x i / η)
       let φ := fun x => ∫ y, f₀ (x - y) * ψ_η y
       eLpNorm (fun x => f₀ x - φ x) 1 volume < ENNReal.ofReal ε₁ ∧
       eLpNorm (fun x => f₀ x - φ x) 2 volume < ENNReal.ofReal ε₂) := by sorry
