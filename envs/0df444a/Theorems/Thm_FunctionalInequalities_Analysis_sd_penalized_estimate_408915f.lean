-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_sd_penalized_estimate_408915f
-- name    : FunctionalInequalities.Analysis.sd_penalized_estimate_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:20:35.378732+00:00
-- url     : https://prove2.me/theorems/eed62f7c-0cdd-40d7-a590-c70d27b453f8
-- title:
--   Penalized Maximum Second-Difference Estimate
-- statement:
--   This is a technical estimate at a penalized maximum of a convex function's second difference.
--
--   Let $E$ be finite-dimensional, let $u,V:E\to\mathbb R$ be differentiable, let $u$ be convex, and let $\kappa>0$. Assume that $V(y)-\frac\kappa2\|y\|^2$ is convex. Suppose there is $C\in\mathbb R$ such that
--
--   $$
--   \left|D V(\nabla u(x))[\nabla u(x)]\right|\leq C
--   $$
--
--   for every $x$. For $\eta>0$, $x_0,h\in E$, assume that the penalized second difference at $x_0$ dominates that at every $y$, and that the corresponding comparison for $V\circ\nabla u-u$ is at most $\eta n$. Then
--
--   $$
--   \Delta_h^2u(x_0)
--   \leq
--   \frac{4\|h\|^2}{\kappa}
--   +2\|h\|\sqrt{\frac{\eta(n+C)}{\kappa}},
--   $$
--
--   where $\Delta_h^2u(x)=u(x+h)+u(x-h)-2u(x)$. This auxiliary estimate is the algebraic maximum-principle step before letting $\eta\downarrow0$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/SecondDifference.lean#L586-L685 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.SecondDifference`, declaration `_private.FunctionalInequalities.Analysis.Convex.SecondDifference.0.FunctionalInequalities.Analysis.sd_penalized_estimate`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open scoped RealInnerProductSpace
section LT17CPenalizedMaximumBound
open Set
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section FiniteDimensional
variable [FiniteDimensional ℝ E]
set_option maxHeartbeats 800000

lemma FunctionalInequalities.Analysis.sd_penalized_estimate_408915f {u V : E → ℝ}
    (hconv : ConvexOn ℝ univ u) (hu : Differentiable ℝ u)
    (hV : Differentiable ℝ V) {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun y => V y - (κ / 2) * ‖y‖ ^ 2))
    {C : ℝ} (hC : ∀ x, |fderiv ℝ V (gradient u x) (gradient u x)| ≤ C)
    (n : ℕ) (h x₀ : E) {η : ℝ} (hη : 0 < η)
    (hmaximum : ∀ y, u (y + h) + u (y - h) - 2 * u y - η * u y ≤
      u (x₀ + h) + u (x₀ - h) - 2 * u x₀ - η * u x₀)
    (hcomparison :
      (V (gradient u (x₀ + h)) - u (x₀ + h)) +
        (V (gradient u (x₀ - h)) - u (x₀ - h)) -
        2 * (V (gradient u x₀) - u x₀) ≤ η * n) :
    u (x₀ + h) + u (x₀ - h) - 2 * u x₀ ≤
      4 * ‖h‖ ^ 2 / κ + 2 * ‖h‖ * Real.sqrt (η * (n + C) / κ) := by sorry
