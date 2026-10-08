-- Prove2me | Theorems.Thm_L0BnB_Strength_eq_37
-- name    : L0BnB.Strength.eq_37
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:33.252331+00:00
-- url     : https://prove2.me/theorems/5899a8b6-5ae8-4cde-8dab-0cadb4d8d6ee
-- title:
--   (37) — the interval relaxation of the Big-M formulation is $\min_{\|\beta\|_\infty\le M} H(\beta)$
-- statement:
--   Let $X\in\mathbb R^{n\times p}$, $y\in\mathbb R^n$, $\lambda_0,\lambda_2>0$ and $M>0$. Let $V_{B(M)}$ be the optimal value of the interval relaxation of the Big-M formulation (2), in which the indicator variables $z_i$ range over $[0,1]$, and let
--
--   $$H(\beta) = \frac12\|y - X\beta\|_2^2 + \sum_{i\in[p]}\Big(\frac{\lambda_0}{M}|\beta_i| + \lambda_2\beta_i^2\Big).$$
--
--   Then $H$ attains its minimum over the box $\|\beta\|_\infty \le M$, and
--
--   $$V_{B(M)} = \min_{\|\beta\|_\infty\le M} H(\beta).$$
--
--   This eliminates the variables $z$ from the Big-M relaxation and expresses it purely in $\beta$-space, which is the form in which it is compared with the perspective relaxation (5).
--
--   **Formalization Note** The statement is `IsLeast (H '' box) V_B(M)`: $V_{B(M)}$ is a value of $H$ on the box and a lower bound for all of them, which is the paper's "min".
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 28, App. A, Proof of Proposition 1, (37)

import Mathlib
import Definitions.Def_L0BnB_Strength_Penalties
import Definitions.Def_L0BnB_Strength_Relaxations

namespace L0BnB.Strength

/-- (37), Proof of Proposition 1, p. 28: the interval relaxation of B(M) has optimal value
`min_{‖β‖_∞ ≤ M} H(β)`; the minimum over the L0BnB.Reduced.box is attained and equals `V_{B(M)}`. -/
theorem eq_37 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 lam2 M : ℝ)
    (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M) :
    IsLeast (H X y lam0 lam2 M '' L0BnB.Reduced.box p M) (VB X y lam0 lam2 M) := by sorry

end L0BnB.Strength
