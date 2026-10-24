-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_secondDifference_le_of_penalized_maxima_408915f
-- name    : FunctionalInequalities.Analysis.secondDifference_le_of_penalized_maxima_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:20:32.090741+00:00
-- url     : https://prove2.me/theorems/ab558626-4486-46e9-8692-c5533500cfd6
-- title:
--   Global Second-Difference Bound from Penalized Maxima
-- statement:
--   This formalizes the algebraic second-difference estimate used in the weak Letwin route.
--
--   Let $E$ be finite-dimensional, let $u,V:E\to\mathbb R$ be differentiable, and assume:
--
--   1. $u$ is convex and bounded below by $m$;
--   2. $\kappa>0$ and $V(y)-\frac\kappa2\|y\|^2$ is convex;
--   3. $|DV(\nabla u(x))[\nabla u(x)]|\leq C$ for every $x$;
--   4. for every $\eta>0$, there exists $x_0$ such that the penalized second difference $\Delta_h^2u(y)-\eta u(y)$ is maximized at $x_0$, and
--      $$
--      (V\circ\nabla u-u)(x_0+h)+(V\circ\nabla u-u)(x_0-h)-2(V\circ\nabla u-u)(x_0)\leq\eta n.
--      $$
--
--   Then for every $x,h\in E$,
--
--   $$
--   \Delta_h^2u(x)\leq\frac{4\|h\|^2}{\kappa}.
--   $$
--
--   The result is a reusable global estimate once penalized maximizers with the stated comparison are available.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/SecondDifference.lean#L687-L732 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.SecondDifference`, declaration `FunctionalInequalities.Analysis.secondDifference_le_of_penalized_maxima`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.secondDifference_le_of_penalized_maxima_408915f {u V : E → ℝ} (hconv : ConvexOn ℝ univ u)
    (hu : Differentiable ℝ u) (hV : Differentiable ℝ V) {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun y => V y - (κ / 2) * ‖y‖ ^ 2)) {C : ℝ}
    (hC : ∀ x, |fderiv ℝ V (gradient u x) (gradient u x)| ≤ C) {m : ℝ} (hm : ∀ x, m ≤ u x)
    (n : ℕ) (h : E)
    (hmax : ∀ η > 0, ∃ x₀ : E,
      (∀ y, u (y + h) + u (y - h) - 2 * u y - η * u y ≤
        u (x₀ + h) + u (x₀ - h) - 2 * u x₀ - η * u x₀) ∧
      (V (gradient u (x₀ + h)) - u (x₀ + h)) + (V (gradient u (x₀ - h)) - u (x₀ - h)) -
        2 * (V (gradient u x₀) - u x₀) ≤ η * n) :
    ∀ x, u (x + h) + u (x - h) - 2 * u x ≤ 4 * ‖h‖ ^ 2 / κ := by sorry
