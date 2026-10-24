-- Prove2me | Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_norm_gradient_scaled_mul_sq_le_408915f
-- name    : FunctionalInequalities.Poincare.SmoothTest.norm_gradient_scaled_mul_sq_le_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:29:31.785154+00:00
-- url     : https://prove2.me/theorems/ac248f9a-436b-4ae4-af6f-a62784d8e43d
-- title:
--   Squared Gradient Bound for a Scaled Cutoff Product
-- statement:
--   This is a pointwise estimate for the gradient of a function multiplied by the designated scaled cutoff.
--
--   Let $E$ be a finite-dimensional complete real inner product space. Denote the fixed bump `Energy.Euclidean.LipschitzApproximation.bump` by $\beta$, and its scaled cutoff `Energy.Euclidean.LipschitzApproximation.scaled R` by $\chi_R$. Assume:
--
--   1. $R,M\in\mathbb R$ and $R>0$.
--   2. $\|D\beta(y)\|\le M$ for every $y\in E$, where the norm is the operator norm of the Fréchet derivative.
--   3. $f:E\to\mathbb R$ is differentiable at $x\in E$.
--
--   Then
--   $$
--   \|\nabla(\chi_R f)(x)\|^2
--   \le 2\|\nabla f(x)\|^2+2(M/R)^2 f(x)^2.
--   $$
--   This technical estimate controls the energy contribution introduced by cutoff multiplication. It requires no measure or global differentiability assumption on $f$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/SmoothTest/WeakLimit.lean#L341-L419 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.SmoothTest.WeakLimit`, declaration `FunctionalInequalities.Poincare.SmoothTest.norm_gradient_scaled_mul_sq_le`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
section
namespace FunctionalInequalities.Poincare.SmoothTest
end FunctionalInequalities.Poincare.SmoothTest
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.SmoothTest
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
section Cutoff
variable [FiniteDimensional ℝ E]
omit [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Poincare.SmoothTest.norm_gradient_scaled_mul_sq_le_408915f {R M : ℝ} (hR : 0 < R)
    (hM : ∀ x : E, ‖fderiv ℝ (⇑(Energy.Euclidean.LipschitzApproximation.bump (E := E))) x‖ ≤ M)
    {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) :
    ‖gradient (fun y => Energy.Euclidean.LipschitzApproximation.scaled R y * f y) x‖ ^ 2 ≤
      2 * ‖gradient f x‖ ^ 2 + 2 * (M / R) ^ 2 * f x ^ 2 := by sorry
