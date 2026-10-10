-- Prove2me | Theorems.Thm_NonconvexDRS_ADMM_eq_5_3a
-- name    : NonconvexDRS.ADMM.eq_5_3a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:32:57.939984+00:00
-- url     : https://prove2.me/theorems/af6901f2-c3b6-4dbd-afe2-e888613b7ab8
-- title:
--   (5.3a), proof of Theorem 5.5, p. 19 — prox_{γφ₁} ⊇ A argmin{f + (1/(2γ))‖A · − s‖²} for φ₁ = (Af)
-- statement:
--   Let $f:\mathbb R^m\to\overline{\mathbb R}$, $A\in\mathbb R^{p\times m}$, $\gamma>0$ and $s\in\mathbb R^p$, and set $\varphi_1=(Af)$. If $x$ minimizes $f+\frac1{2\gamma}\|A\cdot-s\|^2$, then
--   $$Ax\in\operatorname{prox}_{\gamma\varphi_1}(s),\qquad\text{i.e.}\qquad\operatorname{prox}_{\gamma\varphi_1}(s)\supseteq A\operatorname*{arg\,min}\Big\{f+\tfrac1{2\gamma}\|A\cdot-s\|^2\Big\}.$$
--
--   This is the inclusion that turns the ADMM $x$-update into the first proximal step of DRS.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, p. 19, (5.3a) in the proof of Theorem 5.5

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_ADMM_Setting

open NonconvexSplitting.Shared
open Filter Topology
open scoped InnerProductSpace

namespace NonconvexDRS.ADMM

/-- (5.3a), proof of Theorem 5.5, p. 19: with `φ₁ = (Af)`,
`prox_{γφ₁}(s) ⊇ A argmin { f + (1/(2γ))‖A · - s‖² }`. -/
theorem eq_5_3a {m p : ℕ} (f : EuclideanSpace ℝ (Fin m) → EReal)
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (γ : ℝ) (hγ : 0 < γ) (s : EuclideanSpace ℝ (Fin p)) (x : EuclideanSpace ℝ (Fin m))
    (hx : ∀ x', f x + ((‖A x - s‖ ^ 2 / (2 * γ) : ℝ) : EReal) ≤
      f x' + ((‖A x' - s‖ ^ 2 / (2 * γ) : ℝ) : EReal)) :
    A x ∈ NonconvexDRS.Tight.proxSet (imageFn A f) γ s := by sorry

end NonconvexDRS.ADMM
