-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_mul_integral_gamma_le_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.mul_integral_gamma_le_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:05:26.342986+00:00
-- url     : https://prove2.me/theorems/521aff2d-1e3d-4bc4-b485-b71637296861
-- title:
--   Integrated Curvature Bound for Compactly Supported Tests
-- statement:
--   This is the integrated $CD(\rho,\infty)$ inequality for a weighted Laplacian.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $m$ be an additive Haar measure, and let $U,f:E\to\mathbb R$. Assume:
--
--   1. $U$ is $C^2$.
--   2. $f$ is $C^3$ and has compact support.
--   3. For some $\rho\in\mathbb R$, every $x,v\in E$ satisfy
--      $$\rho\|v\|^2\le D^2U(x)[v,v].$$
--
--   With $\mu=m.\operatorname{tilted}(-U)$ and `gamma` given by $\Gamma(f)=\|\nabla f\|^2$,
--
--   $$\rho\int\Gamma(f)\,d\mu\le\int\bigl(\operatorname{weightedLaplacian}(U,f)\bigr)^2\,d\mu.$$
--
--   This is the integrated coercivity estimate obtained from a pointwise Hessian lower bound and is useful in weighted diffusion arguments.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Curvature.lean#L209-L252 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Curvature`, declaration `FunctionalInequalities.Analysis.BakryEmery.mul_integral_gamma_le`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted

noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E] (m : Measure E) [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Analysis.BakryEmery.mul_integral_gamma_le_408915f {U f : E → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 3 f)
    (hfc : HasCompactSupport f) {ρ : ℝ}
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) :
    ρ * ∫ x, gamma f f x ∂(m.tilted (-U)) ≤ ∫ x, weightedLaplacian U f x ^ 2 ∂(m.tilted (-U)) := by sorry
