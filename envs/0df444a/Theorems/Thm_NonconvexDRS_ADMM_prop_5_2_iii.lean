-- Prove2me | Theorems.Thm_NonconvexDRS_ADMM_prop_5_2_iii
-- name    : NonconvexDRS.ADMM.prop_5_2_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:33:01.750669+00:00
-- url     : https://prove2.me/theorems/499a5d98-f3c6-4675-b530-fe2f90bf1029
-- title:
--   Proposition 5.2(iii), p. 18 — prox_{(Ch)/β} ⊇ C X_β
-- statement:
--   Let $h:\mathbb R^n\to\overline{\mathbb R}$, $C\in\mathbb R^{p\times n}$, $\beta>0$ and $s\in\mathbb R^p$. For every $x_\beta\in X_\beta(s)=\operatorname*{arg\,min}_x\{h(x)+\frac\beta2\|Cx-s\|^2\}$,
--   $$Cx_\beta\in\operatorname{prox}_{(Ch)/\beta}(s)=\operatorname*{arg\,min}_{t\in\mathbb R^p}\Big\{(Ch)(t)+\tfrac\beta2\|t-s\|^2\Big\}.$$
--
--   Minimizing over $x$ and then mapping by $C$ thus produces a proximal point of the image function; this is the mechanism behind both prox-inclusions of the ADMM–DRS equivalence.
--
--   **Formalization Note** The proximal mapping is the set `proxSet` with stepsize $1/\beta$. The global hypothesis $X_\beta(s')\neq\emptyset$ for all $s'$ is dropped, which makes the statement stronger.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, pp. 17–18, Proposition 5.2(iii)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_ADMM_Setting

open NonconvexSplitting.Shared
open Filter Topology
open scoped InnerProductSpace

namespace NonconvexDRS.ADMM

/-- Proposition 5.2(iii), p. 18: `prox_{(Ch)/β}(s) ⊇ C X_β(s)`, i.e. `C x_β` is a proximal point of
`(Ch)` with stepsize `1/β` at `s`, for every `s` and every `x_β ∈ X_β(s)`. -/
theorem prop_5_2_iii {n p : ℕ} (h : EuclideanSpace ℝ (Fin n) → EReal)
    (C : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (β : ℝ) (hβ : 0 < β) (s : EuclideanSpace ℝ (Fin p))
    (xβ : EuclideanSpace ℝ (Fin n)) (hxβ : xβ ∈ Xbeta h C β s) :
    C xβ ∈ NonconvexDRS.Tight.proxSet (imageFn C h) (1 / β) s := by sorry

end NonconvexDRS.ADMM
