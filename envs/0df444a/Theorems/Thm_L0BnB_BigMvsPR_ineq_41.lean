-- Prove2me | Theorems.Thm_L0BnB_BigMvsPR_ineq_41
-- name    : L0BnB.BigMvsPR.ineq_41
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:28:45.00599+00:00
-- url     : https://prove2.me/theorems/4810bf07-11f2-45e0-b08e-88afae361b60
-- title:
--   (41) — $v^*(M) \ge V_{B(M)}$ for $M \ge \sqrt{\lambda_0/\lambda_2}$
-- statement:
--   Let $X \in \mathbb R^{n\times p}$, $y \in \mathbb R^n$ and $\lambda_0, \lambda_2, M > 0$. Let $V_{B(M)}$ be the optimal value of the interval relaxation of the Big-M formulation (2), $G$ the objective of (6), and
--
--   $$v^*(M) = \min_{\|\beta\|_\infty \le M} G(\beta)$$
--
--   the minimum of $G$ over the box. If $M \ge \sqrt{\lambda_0/\lambda_2}$, then
--
--   $$v^*(M) \ge V_{B(M)}.$$
--
--   Combined with the hypothesis $\lambda_2 \in \mathcal L(M)$, which places a minimizer of $G$ inside the box so that $v^*(M) = V_{PR(\infty)}$, this yields (11).
--
--   **Formalization Note** $v^*(M)$ is the real infimum of $G$ over the box (`vStar`); the paper's $\min$ is attained since $G$ is continuous and the box is compact.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 29, App. A, Proof of (11), (41)

import Mathlib
import Definitions.Def_L0BnB_BigMvsPR_Penalties
import Definitions.Def_L0BnB_BigMvsPR_Relaxations

namespace L0BnB.BigMvsPR

/-- (41), Proof of (11), p. 29: with `v*(M) = min_{‖β‖_∞ ≤ M} L0BnB.Strength.G(β)`, if `M ≥ √(λ₀/λ₂)` then
`v*(M) ≥ V_{B(M)}`. -/
theorem ineq_41 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 lam2 M : ℝ)
    (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hMlarge : Real.sqrt (lam0 / lam2) ≤ M) :
    L0BnB.Strength.VB X y lam0 lam2 M ≤ vStar X y lam0 lam2 M := by sorry

end L0BnB.BigMvsPR
