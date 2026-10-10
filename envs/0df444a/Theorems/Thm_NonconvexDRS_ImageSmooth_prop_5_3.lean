-- Prove2me | Theorems.Thm_NonconvexDRS_ImageSmooth_prop_5_3
-- name    : NonconvexDRS.ImageSmooth.prop_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:43.785759+00:00
-- url     : https://prove2.me/theorems/7b929593-618f-4b95-a561-4b946fd18776
-- title:
--   Proposition 5.3, p. 18 — Cᵀ∂̂(Ch)(s̄) ⊆ ∂̂h(x̄) for every minimizer x̄ of h on the fibre Cx = s̄
-- statement:
--   Let $h:\mathbb R^n\to\overline{\mathbb R}$ and $C\in\mathbb R^{p\times n}$, and let
--   $$X(s)=\operatorname*{arg\,min}_{x\in\mathbb R^n}\{h(x)\mid Cx=s\}.$$
--   Then for every $\bar s\in C\operatorname{dom}h$ and every $\bar x\in X(\bar s)$,
--   $$C^\top\hat\partial(Ch)(\bar s)\subseteq\hat\partial h(\bar x),$$
--   where $\hat\partial$ denotes the regular (Fréchet) subdifferential (2.1). That is, if $v$ is a regular subgradient of the image function $(Ch)$ at $\bar s$, then $C^\top v$ is a regular subgradient of $h$ at $\bar x$.
--
--   This transfers first-order information from the image function back to the original function; Theorem 5.13 uses it to express subgradients of $(Af)$ through gradients of $f$.
--
--   **Formalization Note** $h$ never takes the value $-\infty$ (the codomain $\overline{\mathbb R}=\mathbb R\cup\{\infty\}$ of the page). The regular subdifferential is the published `NonconvexSplitting.Shared.IsRegularSubgrad`, the $\varepsilon$-form of the liminf in (2.1). $\bar x\in X(\bar s)$ is written as $C\bar x=\bar s$ and $h(\bar x)\le h(x)$ for all $x$ with $Cx=\bar s$.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, p. 18, Proposition 5.3 (proof pp. 28–29)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_ImageSmooth_Setting

open NonconvexSplitting.Shared
open scoped InnerProductSpace

namespace NonconvexDRS.ImageSmooth

/-- Proposition 5.3, p. 18: for `h : ℝⁿ → ℝ̄`, `s̄ ∈ C dom h` and `x̄ ∈ X(s̄) = argmin {h(x) | Cx = s̄}`,
every regular subgradient `v ∈ ∂̂(Ch)(s̄)` gives `Cᵀv ∈ ∂̂h(x̄)`. -/
theorem prop_5_3 {n p : ℕ} (h : EuclideanSpace ℝ (Fin n) → EReal) (hbot : ∀ x, h x ≠ ⊥)
    (C : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (sbar : EuclideanSpace ℝ (Fin p)) (hs : ∃ x, C x = sbar ∧ h x ≠ ⊤)
    (xbar : EuclideanSpace ℝ (Fin n)) (hxbar : C xbar = sbar ∧ ∀ x, C x = sbar → h xbar ≤ h x)
    (v : EuclideanSpace ℝ (Fin p)) (hv : IsRegularSubgrad (imageFn C h) sbar v) :
    IsRegularSubgrad h xbar (ContinuousLinearMap.adjoint C v) := by sorry

end NonconvexDRS.ImageSmooth
