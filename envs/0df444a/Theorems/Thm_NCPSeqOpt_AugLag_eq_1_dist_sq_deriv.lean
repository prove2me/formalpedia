-- Prove2me | Theorems.Thm_NCPSeqOpt_AugLag_eq_1_dist_sq_deriv
-- name    : NCPSeqOpt.AugLag.eq_1_dist_sq_deriv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:25.216422+00:00
-- url     : https://prove2.me/theorems/82a8d9d4-9b15-4521-8684-ec39f6a897c8
-- title:
--   (1), p. 3 — dist²_K is C¹ with derivative 2(w − Π_K(w))
-- statement:
--   Let $\mathbb E$ be a finite-dimensional real inner product space and $\mathcal K\subseteq\mathbb E$ a nonempty closed convex cone. Write $\operatorname{dist}_{\mathcal K}(w)=\min\{\|w-v\|:v\in\mathcal K\}$. Then $w\mapsto\operatorname{dist}^2_{\mathcal K}(w)$ is continuously differentiable, and its gradient is
--   $$D(\operatorname{dist}^2_{\mathcal K})(w)=2\big(w-\Pi_{\mathcal K}(w)\big)\qquad\text{for every }w\in\mathbb E. \tag{1}$$
--
--   Formula (1) is what yields the derivative (20) of the augmented Lagrangian and the derivative of $\Psi(x)=\tfrac12\|\Pi_{\mathcal K^\circ}(G(x))\|^2$ used in Theorem 4.2.
--
--   **Formalization Note** $\operatorname{dist}_{\mathcal K}$ is Mathlib's `Metric.infDist`, an infimum, which equals the page's minimum for a nonempty closed set. The derivative is stated as a gradient (`HasGradientAt`) at every point, together with `ContDiff ℝ 1`.
-- source:
--   Andreani, Gómez, Haeser, Mito & Ramos, On Optimality Conditions for Nonlinear Conic Programming, author's manuscript (revised 2021-04-20; Math. Oper. Res. doi:10.1287/moor.2021.1203), §2.1, (1), p. 3

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_NCPSeqOpt_AugLag_Setting

namespace NCPSeqOpt.AugLag

open MoreauProx.Decomposition
open scoped InnerProductSpace
open Filter Topology

theorem eq_1_dist_sq_deriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Set E) (hK : IsClosedConvexCone K) :
    ContDiff ℝ 1 (fun v => Metric.infDist v K ^ 2) ∧
      ∀ w : E, HasGradientAt (fun v => Metric.infDist v K ^ 2) ((2 : ℝ) • (w - proj K w)) w := by sorry

end NCPSeqOpt.AugLag
