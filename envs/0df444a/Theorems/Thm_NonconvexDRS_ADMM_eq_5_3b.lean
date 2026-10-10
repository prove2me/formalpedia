-- Prove2me | Theorems.Thm_NonconvexDRS_ADMM_eq_5_3b
-- name    : NonconvexDRS.ADMM.eq_5_3b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:33:08.2725+00:00
-- url     : https://prove2.me/theorems/04cfe0d9-8d57-4293-b2a0-fea0d09e931c
-- title:
--   (5.3b), proof of Theorem 5.5, p. 19 — prox_{γφ₂} ⊇ b − B argmin{g + (1/(2γ))‖B · + s − b‖²} for φ₂ = (Bg)(b − ·)
-- statement:
--   Let $g:\mathbb R^n\to\overline{\mathbb R}$, $B\in\mathbb R^{p\times n}$, $b\in\mathbb R^p$, $\gamma>0$ and $s\in\mathbb R^p$, and set $\varphi_2(t)=(Bg)(b-t)$. If $z$ minimizes $g+\frac1{2\gamma}\|B\cdot+s-b\|^2$, then
--   $$b-Bz\in\operatorname{prox}_{\gamma\varphi_2}(s),\qquad\text{i.e.}\qquad\operatorname{prox}_{\gamma\varphi_2}(s)\supseteq b-B\operatorname*{arg\,min}\Big\{g+\tfrac1{2\gamma}\|B\cdot+s-b\|^2\Big\}.$$
--
--   This is the inclusion that turns the ADMM $z$-update into the second proximal step of DRS.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, p. 19, (5.3b) in the proof of Theorem 5.5

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_ADMM_Setting

open NonconvexSplitting.Shared
open Filter Topology
open scoped InnerProductSpace

namespace NonconvexDRS.ADMM

/-- (5.3b), proof of Theorem 5.5, p. 19: with `φ₂ = (Bg)(b - ·)`,
`prox_{γφ₂}(s) ⊇ b - B argmin { g + (1/(2γ))‖B · + s - b‖² }`. -/
theorem eq_5_3b {n p : ℕ} (g : EuclideanSpace ℝ (Fin n) → EReal)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p)) (b : EuclideanSpace ℝ (Fin p))
    (γ : ℝ) (hγ : 0 < γ) (s : EuclideanSpace ℝ (Fin p)) (z : EuclideanSpace ℝ (Fin n))
    (hz : ∀ z', g z + ((‖B z + s - b‖ ^ 2 / (2 * γ) : ℝ) : EReal) ≤
      g z' + ((‖B z' + s - b‖ ^ 2 / (2 * γ) : ℝ) : EReal)) :
    b - B z ∈ NonconvexDRS.Tight.proxSet (fun t => imageFn B g (b - t)) γ s := by sorry

end NonconvexDRS.ADMM
