-- Prove2me | Theorems.Thm_NonconvexDRS_ADMM_prop_5_3
-- name    : NonconvexDRS.ADMM.prop_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:32:47.324013+00:00
-- url     : https://prove2.me/theorems/c09598db-5495-486c-968b-609f50fdeb0f
-- title:
--   Proposition 5.3, p. 18 — Cᵀ∂̂(Ch)(s̄) ⊆ ∂̂h(x̄) for s̄ ∈ C dom h and x̄ ∈ argmin{h | Cx = s̄}
-- statement:
--   Let $h:\mathbb R^n\to\overline{\mathbb R}$ and $C\in\mathbb R^{p\times n}$, and let $X(s)=\operatorname*{arg\,min}_{x}\{h(x)\mid Cx=s\}$. For every $\bar s\in C\operatorname{dom}h$, every $\bar x\in X(\bar s)$ and every regular subgradient $v\in\hat\partial(Ch)(\bar s)$,
--   $$C^\top v\in\hat\partial h(\bar x),\qquad\text{i.e.}\qquad C^\top\hat\partial(Ch)(\bar s)\subseteq\hat\partial h(\bar x).$$
--   Here $\hat\partial$ is the regular (Fréchet) subdifferential (2.1).
--
--   It transfers first-order information from the image function back to $h$; in the proof of Theorem 5.5 it gives an alternative derivation of $-A^\top y^+\in\hat\partial f(x^+)$.
--
--   **Formalization Note** $\bar x\in X(\bar s)$ is written as $C\bar x=\bar s$ and $h(\bar x)\le h(x)$ for every $x$ with $Cx=\bar s$. $\hat\partial$ is the published `IsRegularSubgrad`, which requires a finite value at the base point.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, p. 18, Proposition 5.3

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_ADMM_Setting

open NonconvexSplitting.Shared
open Filter Topology
open scoped InnerProductSpace

namespace NonconvexDRS.ADMM

/-- Proposition 5.3, p. 18: for `s̄ ∈ C dom h` and `x̄ ∈ X(s̄) = argmin {h(x) | Cx = s̄}`,
`Cᵀ ∂̂(Ch)(s̄) ⊆ ∂̂h(x̄)`. -/
theorem prop_5_3 {n p : ℕ} (h : EuclideanSpace ℝ (Fin n) → EReal)
    (C : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (sbar : EuclideanSpace ℝ (Fin p)) (hsbar : sbar ∈ C '' {x | h x ≠ ⊤})
    (xbar : EuclideanSpace ℝ (Fin n)) (hxbar : C xbar = sbar ∧ ∀ x, C x = sbar → h xbar ≤ h x)
    (v : EuclideanSpace ℝ (Fin p)) (hv : IsRegularSubgrad (imageFn C h) sbar v) :
    IsRegularSubgrad h xbar (ContinuousLinearMap.adjoint C v) := by sorry

end NonconvexDRS.ADMM
