-- Prove2me | Theorems.Thm_GradSampling_Conv_Gset_subset_epsSubdiff
-- name    : GradSampling.Conv.Gset_subset_epsSubdiff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:48:29.348208+00:00
-- url     : https://prove2.me/theorems/d6c5402b-2022-42fe-8353-84d2d527cc36
-- title:
--   §2, p. 754 — G_ε(x) ⊂ ∂̄_ε f(x)
-- statement:
--   Let $D$ be open, $f$ continuously differentiable on $D$, and $\epsilon>0$. Then for every $x\in\mathbb R^n$
--
--   $$G_\epsilon(x)\subseteq\bar\partial_\epsilon f(x).$$
--
--   So $\rho_\epsilon(x)=0$ implies that $x$ is Clarke $\epsilon$-stationary.
--
--   **Formalization Note** Neither local Lipschitz continuity nor density of $D$ is needed, so both are dropped.
-- source:
--   Burke, Lewis, Overton, A robust gradient sampling algorithm for nonsmooth, nonconvex optimization, SIAM J. Optim. 15 (2005), p. 754, §2, "Clearly, G_ε(x) ⊂ ∂̄_ε f(x)"

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_GradSampling_Conv_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace GradSampling.Conv

/-- §2, p. 754: `G_ε(x) ⊂ ∂̄_ε f(x)`. -/
theorem Gset_subset_epsSubdiff {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (D : Set (EuclideanSpace ℝ (Fin n)))
    (hDo : IsOpen D) (hC1 : ContDiffOn ℝ 1 f D) (ε : ℝ) (hε : 0 < ε) :
    ∀ x, Gset f D ε x ⊆ epsSubdiff f ε x := by sorry

end GradSampling.Conv
