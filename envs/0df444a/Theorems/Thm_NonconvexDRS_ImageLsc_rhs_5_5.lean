-- Prove2me | Theorems.Thm_NonconvexDRS_ImageLsc_rhs_5_5
-- name    : NonconvexDRS.ImageLsc.rhs_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:39.68338+00:00
-- url     : https://prove2.me/theorems/992325a3-bee5-47d8-a286-a43f85ddc3d3
-- title:
--   Proof of Theorem 5.11, p. 24 — the right-hand side of (5.5) is (Bg)(Bz̄)
-- statement:
--   Let $g:\mathbb R^n\to\overline{\mathbb R}$ be any function, $B\in\mathbb R^{p\times n}$ a matrix and $\bar z\in\mathbb R^n$. Then the right-hand side of condition (5.5) is the value of the image function $(Bg)$ at $B\bar z$:
--   $$\inf_{d\in\ker B} g(\bar z+d)=(Bg)(B\bar z)=\inf\{g(z)\mid Bz=B\bar z\}.$$
--
--   Verbatim (p. 24): "Proof. Observe first that the right-hand side in (5.5) is (Bg)(B$\bar z$)."
--
--   This identity is the first step of both directions of Theorem 5.11: it lets condition (5.5) be read as a comparison between $(Bg)(B\bar z)$ and the values of $g$ far out along directions that $B$ nearly annihilates.
--
--   **Formalization Note** No hypothesis on $g$ is needed; both sides are infima in $[-\infty,+\infty]$.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, p. 24, proof of Theorem 5.11, first sentence

import Mathlib
import Definitions.Def_NonconvexDRS_ImageLsc_Setting

namespace NonconvexDRS.ImageLsc

theorem rhs_5_5 {n p : ℕ} (g : EuclideanSpace ℝ (Fin n) → EReal)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (zbar : EuclideanSpace ℝ (Fin n)) :
    (⨅ (d : EuclideanSpace ℝ (Fin n)) (_ : B d = 0), g (zbar + d)) = NonconvexDRS.ADMM.imageFn B g (B zbar) := by sorry

end NonconvexDRS.ImageLsc
