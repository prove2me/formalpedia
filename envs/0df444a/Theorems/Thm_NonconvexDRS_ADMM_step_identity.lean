-- Prove2me | Theorems.Thm_NonconvexDRS_ADMM_step_identity
-- name    : NonconvexDRS.ADMM.step_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:32:48.128764+00:00
-- url     : https://prove2.me/theorems/2338dfbb-f399-4653-b9cc-961e72a993bc
-- title:
--   Proof of Theorem 5.5, p. 19 — the relaxed ADMM multiplier updates give s + λ(v − u) = s⁺
-- statement:
--   Let $A\in\mathbb R^{p\times m}$, $B\in\mathbb R^{p\times n}$, $b\in\mathbb R^p$, $\beta>0$ and $\lambda\in\mathbb R$. Given $x,x^+\in\mathbb R^m$, $z\in\mathbb R^n$, $y\in\mathbb R^p$, let the multipliers be updated as in ADMM,
--   $$y^{+/2}=y-\beta(1-\lambda)(Ax+Bz-b),\qquad y^+=y^{+/2}+\beta(Ax^++Bz-b).$$
--   With $s=Ax-y/\beta$, $u=Ax$, $v=b-Bz$ and $s^+=Ax^+-y^+/\beta$ as in (5.2),
--   $$s^+=s+\lambda(v-u).$$
--
--   This is the DRS update of the governing sequence, read off the two multiplier updates of ADMM.
--
--   **Formalization Note** $\lambda$ is unrestricted here; only $\beta\neq0$ is used, and the page's $\beta>0$ is kept.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, p. 19, proof of Theorem 5.5 (first display)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_ADMM_Setting

open NonconvexSplitting.Shared
open Filter Topology
open scoped InnerProductSpace

namespace NonconvexDRS.ADMM

/-- The first relation in the proof of Theorem 5.5, p. 19: with `s, u, v, s⁺` as in (5.2) and
`y⁺` produced from `(x, y, z, x⁺)` by the two multiplier updates of (ADMM),
`s + λ(v - u) = s⁺`. -/
theorem step_identity {m n p : ℕ}
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p)) (b : EuclideanSpace ℝ (Fin p))
    (β lam : ℝ) (hβ : 0 < β)
    (x xp : EuclideanSpace ℝ (Fin m)) (y yh yp : EuclideanSpace ℝ (Fin p))
    (z : EuclideanSpace ℝ (Fin n))
    (hyh : yh = y - (β * (1 - lam)) • (A x + B z - b))
    (hyp : yp = yh + β • (A xp + B z - b)) :
    A xp - (1 / β) • yp = (A x - (1 / β) • y) + lam • ((b - B z) - A x) := by sorry

end NonconvexDRS.ADMM
