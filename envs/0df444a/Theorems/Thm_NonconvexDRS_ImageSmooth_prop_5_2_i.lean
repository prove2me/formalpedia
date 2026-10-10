-- Prove2me | Theorems.Thm_NonconvexDRS_ImageSmooth_prop_5_2_i
-- name    : NonconvexDRS.ImageSmooth.prop_5_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:29.372681+00:00
-- url     : https://prove2.me/theorems/2185f3be-163a-4547-b90d-bd1aacb22d46
-- title:
--   Proposition 5.2(i), p. 18 — if the penalized argmin X_β(s) is nonempty for all s, the image function (Ch) is proper
-- statement:
--   Let $h:\mathbb R^n\to\overline{\mathbb R}$ be proper and $C\in\mathbb R^{p\times n}$. Suppose that for some $\beta>0$ the set-valued mapping
--   $$X_\beta(s)=\operatorname*{arg\,min}_{x\in\mathbb R^n}\Big\{h(x)+\tfrac\beta2\|Cx-s\|^2\Big\}$$
--   is nonempty for every $s\in\mathbb R^p$. Then the image function $(Ch)(s)=\inf\{h(x)\mid Cx=s\}$ is proper: it never takes the value $-\infty$, and it is finite at some point.
--
--   In the proof of Theorem 5.13 this is the first step: it makes $(Af)$ a proper function, so that its lower semicontinuity and subdifferentials can be discussed.
--
--   **Formalization Note** The page states the proposition for any $h:\mathbb R^n\to\overline{\mathbb R}$; properness of $h$ is added because it is necessary: for $h\equiv+\infty$ every $X_\beta(s)=\mathbb R^n$ is nonempty but $(Ch)\equiv+\infty$ is not proper. Nonemptiness of $X_\beta(s)$ is written as the existence of a minimizer of the penalized objective.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, pp. 17–18, Proposition 5.2(i)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_ImageSmooth_Setting

open NonconvexSplitting.Shared
open scoped InnerProductSpace

namespace NonconvexDRS.ImageSmooth

/-- Proposition 5.2(i), p. 18: if `h : ℝⁿ → ℝ̄` is proper and, for some `β > 0`, the mapping
`X_β(s) = argmin_x {h(x) + (β/2)‖Cx - s‖²}` is nonempty for every `s`, then the image function
`(Ch)` is proper (never `-∞`, finite somewhere). Properness of `h` is a necessary addition. -/
theorem prop_5_2_i {n p : ℕ} (h : EuclideanSpace ℝ (Fin n) → EReal) (hh : NonconvexDRS.DRS.IsProper h)
    (C : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p)) (β : ℝ) (hβ : 0 < β)
    (hX : ∀ s : EuclideanSpace ℝ (Fin p), ∃ xβ : EuclideanSpace ℝ (Fin n), ∀ x,
      h xβ + ((β / 2 * ‖C xβ - s‖ ^ 2 : ℝ) : EReal) ≤ h x + ((β / 2 * ‖C x - s‖ ^ 2 : ℝ) : EReal)) :
    NonconvexDRS.DRS.IsProper (imageFn C h) := by sorry

end NonconvexDRS.ImageSmooth
