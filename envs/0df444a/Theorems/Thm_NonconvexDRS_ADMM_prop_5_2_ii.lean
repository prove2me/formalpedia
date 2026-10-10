-- Prove2me | Theorems.Thm_NonconvexDRS_ADMM_prop_5_2_ii
-- name    : NonconvexDRS.ADMM.prop_5_2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:32:59.568298+00:00
-- url     : https://prove2.me/theorems/7331d6fe-b297-4be1-88fb-7dd95a6f9bcf
-- title:
--   Proposition 5.2(ii), p. 18 — (Ch)(Cx_β) = h(x_β) for every x_β ∈ X_β(s)
-- statement:
--   Let $h:\mathbb R^n\to\overline{\mathbb R}$, $C\in\mathbb R^{p\times n}$, $\beta>0$ and $s\in\mathbb R^p$, and let $x_\beta$ be a minimizer of $h+\frac\beta2\|C\cdot-s\|^2$, i.e. $x_\beta\in X_\beta(s)$. Then
--   $$(Ch)(Cx_\beta)=h(x_\beta),$$
--   that is, $x_\beta$ attains the infimum defining the image function at $Cx_\beta$.
--
--   This identifies the value of the image function at the points the ADMM $x$-update produces.
--
--   **Formalization Note** The equality is in $[-\infty,+\infty]$. The proposition's standing hypothesis that $X_\beta(s')$ is nonempty for every $s'$ is not needed for this item and is dropped, which makes the statement stronger.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, pp. 17–18, Proposition 5.2(ii)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_ADMM_Setting

open NonconvexSplitting.Shared
open Filter Topology
open scoped InnerProductSpace

namespace NonconvexDRS.ADMM

/-- Proposition 5.2(ii), p. 18: `(Ch)(Cx_β) = h(x_β)` for every `s` and every `x_β ∈ X_β(s)`. -/
theorem prop_5_2_ii {n p : ℕ} (h : EuclideanSpace ℝ (Fin n) → EReal)
    (C : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (β : ℝ) (hβ : 0 < β) (s : EuclideanSpace ℝ (Fin p))
    (xβ : EuclideanSpace ℝ (Fin n)) (hxβ : xβ ∈ Xbeta h C β s) :
    imageFn C h (C xβ) = h xβ := by sorry

end NonconvexDRS.ADMM
