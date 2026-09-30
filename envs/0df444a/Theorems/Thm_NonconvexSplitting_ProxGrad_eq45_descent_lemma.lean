-- Prove2me | Theorems.Thm_NonconvexSplitting_ProxGrad_eq45_descent_lemma
-- name    : NonconvexSplitting.ProxGrad.eq45_descent_lemma
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T19:18:39.041197+00:00
-- url     : https://prove2.me/theorems/fbe6a4da-2cb8-4e2d-95d5-0c33064d606c
-- title:
--   Eq. (45): descent inequality for $h + q$ under (44)
-- statement:
--   Let $h, q : \mathbb{R}^n \to \mathbb{R}$ be twice continuously differentiable and $\ell > 0$, and suppose condition (44) holds: $-\ell I \preceq \nabla^2 h(x) + \nabla^2 q(x) \preceq \ell I$ for all $x$. Then for all $u, v \in \mathbb{R}^n$,
--   $$
--   (h + q)(v) \le (h + q)(u) + \langle \nabla h(u) + \nabla q(u),\, v - u\rangle + \frac{\ell}{2}\|v - u\|^2 .
--   $$
--
--   In the paper this is applied at $(u, v) = (x^t, x^{t+1})$; it is the first step of the sufficient-decrease estimate (46).
--
--   **Formalization Note** Stated for all pairs $(u, v)$, the form the paper's justification ("$\nabla(h+q)$ is Lipschitz continuous with modulus at most $\ell$") yields; convexity of $q$ is not needed here.
-- source:
--   Li & Pong, Global Convergence of Splitting Methods for Nonconvex Composite Optimization, arXiv:1407.0753v6, p. 18, Eq. (45)

import Mathlib
import Definitions.Def_NonconvexSplitting_ProxGrad_HessianSandwich

open scoped InnerProductSpace

namespace NonconvexSplitting.ProxGrad

/-- Eq. (45) of Li–Pong (p. 18), in its two-point form: under (44), `∇(h + q)` is
`ℓ`-Lipschitz, so `(h+q)(v) ≤ (h+q)(u) + ⟪∇h(u) + ∇q(u), v - u⟫ + (ℓ/2)‖v - u‖²`. -/
theorem eq45_descent_lemma {n : ℕ} (h q : EuclideanSpace ℝ (Fin n) → ℝ) (ℓ : ℝ)
    (hh : ContDiff ℝ 2 h) (hq : ContDiff ℝ 2 q) (hℓ : 0 < ℓ) (h44 : HessianSandwich h q ℓ)
    (u v : EuclideanSpace ℝ (Fin n)) :
    h v + q v ≤ h u + q u + ⟪gradient h u + gradient q u, v - u⟫_ℝ + ℓ / 2 * ‖v - u‖ ^ 2 := by sorry

end NonconvexSplitting.ProxGrad
