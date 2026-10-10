-- Prove2me | Theorems.Thm_NonconvexDRS_ADMM_prop_5_2_i
-- name    : NonconvexDRS.ADMM.prop_5_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:32:39.35424+00:00
-- url     : https://prove2.me/theorems/83de4df3-1bf5-45d0-b909-9112034c6662
-- title:
--   Proposition 5.2(i), p. 18 — if X_β(s) ≠ ∅ for all s and h is proper, the image function (Ch) is proper
-- statement:
--   Let $h:\mathbb R^n\to\overline{\mathbb R}$ be proper, let $C\in\mathbb R^{p\times n}$, and suppose that for some $\beta>0$ the set
--   $$X_\beta(s)=\operatorname*{arg\,min}_{x\in\mathbb R^n}\Big\{h(x)+\tfrac\beta2\|Cx-s\|^2\Big\}$$
--   is nonempty for every $s\in\mathbb R^p$. Then the image function $(Ch)(s)=\inf\{h(x)\mid Cx=s\}$ is proper: it never equals $-\infty$, and it is finite somewhere.
--
--   A priori an image function can take the value $-\infty$; this proposition is what makes the proximal mapping of $(Af)$ meaningful in the ADMM–DRS equivalence.
--
--   **Formalization Note** The page does not state that $h$ is proper; it is added because for $h\equiv+\infty$ every $X_\beta(s)$ is all of $\mathbb R^n$ while $(Ch)\equiv+\infty$ is not proper. Properness here includes $(Ch)>-\infty$ everywhere.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, pp. 17–18, Proposition 5.2(i)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_ADMM_Setting

open NonconvexSplitting.Shared
open Filter Topology
open scoped InnerProductSpace

namespace NonconvexDRS.ADMM

/-- Proposition 5.2(i), p. 18: if `X_β(s)` is nonempty for every `s` (for some `β > 0`) and `h`
is proper, the image function `(Ch)` is proper. -/
theorem prop_5_2_i {n p : ℕ} (h : EuclideanSpace ℝ (Fin n) → EReal)
    (C : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (β : ℝ) (hβ : 0 < β) (hh : NonconvexDRS.Tight.IsProper h)
    (hX : ∀ s, (Xbeta h C β s).Nonempty) :
    NonconvexDRS.Tight.IsProper (imageFn C h) := by sorry

end NonconvexDRS.ADMM
