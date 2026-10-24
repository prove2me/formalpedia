-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_contDiff_approx_of_lipschitz_gradient_408915f
-- name    : FunctionalInequalities.Analysis.exists_contDiff_approx_of_lipschitz_gradient_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:02:56.030054+00:00
-- url     : https://prove2.me/theorems/0358a475-d7a5-4cc1-b986-88c5d4f86183
-- title:
--   Smooth Approximation with Uniform Gradient Control
-- statement:
--   This gives a smooth approximation scheme for a function with Lipschitz gradient.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel structure. Let $U:E\to\mathbb R$ be $C^1$, and suppose that $\nabla U$ is Lipschitz with constant $G\in[0,\infty)$. Then there exists a sequence $U_k:E\to\mathbb R$ such that:
--
--   1. Every $U_k$ is $C^\infty$.
--   2. For every $k$ and $x\in E$,
--      $$
--      \|\nabla U_k(x)-\nabla U(x)\|\leq \frac{G}{k+1}.
--      $$
--   3. Every $\nabla U_k$ is Lipschitz with the same constant $G$.
--   4. For every $x$, $U_k(x)\to U(x)$ as $k\to\infty$.
--   5. For almost every $x$ with respect to volume measure, $D(\nabla U_k)(x)$ converges to $D(\nabla U)(x)$ as $k\to\infty$.
--
--   The sequence is a reusable regularization device preserving the Lipschitz-gradient bound while providing almost-everywhere Hessian convergence.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Mollification/Hessian.lean#L268-L473 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Mollification.Hessian`, declaration `FunctionalInequalities.Analysis.exists_contDiff_approx_of_lipschitz_gradient`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.SpecificCodomains.Pi

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section StructuredSpace
variable {E : Type*}
variable [NormedAddCommGroup E]
section FiniteDimensional
variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.exists_contDiff_approx_of_lipschitz_gradient_408915f
    {U : E → ℝ} (hU : ContDiff ℝ 1 U) {G : NNReal} (hG : LipschitzWith G (gradient U)) :
    ∃ Uk : ℕ → E → ℝ, (∀ k, ContDiff ℝ ∞ (Uk k)) ∧
      (∀ k x, ‖gradient (Uk k) x - gradient U x‖ ≤ G / ((k : ℝ) + 1)) ∧
      (∀ k, LipschitzWith G (gradient (Uk k))) ∧
      (∀ x, Tendsto (fun k => Uk k x) atTop (𝓝 (U x))) ∧
      (∀ᵐ x ∂(volume : Measure E), Tendsto (fun k => fderiv ℝ (gradient (Uk k)) x) atTop
        (𝓝 (fderiv ℝ (gradient U) x))) := by sorry
