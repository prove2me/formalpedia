-- Prove2me | Theorems.Thm_L0BnB_BigMvsPR_eq_37
-- name    : L0BnB.BigMvsPR.eq_37
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:28:48.870344+00:00
-- url     : https://prove2.me/theorems/6efb6923-e1ce-48a8-80cb-5a76a89941fb
-- title:
--   (37) — the Big-M interval relaxation equals $\min_{\|\beta\|_\infty\le M} H(\beta)$
-- statement:
--   Let $X \in \mathbb R^{n\times p}$, $y \in \mathbb R^n$ and $\lambda_0, \lambda_2, M > 0$. The optimal value of the interval relaxation of the Big-M formulation (2) equals the minimum of
--
--   $$H(\beta) = \tfrac12\|y - X\beta\|_2^2 + \sum_{i\in[p]}\Big(\frac{\lambda_0}{M}|\beta_i| + \lambda_2\beta_i^2\Big)$$
--
--   over the box $\|\beta\|_\infty \le M$:
--
--   $$V_{B(M)} = \min_{\|\beta\|_\infty\le M} H(\beta),$$
--
--   and the minimum is attained.
--
--   This eliminates the relaxed indicator variables $z$ from the Big-M relaxation and expresses it in $\beta$ alone, which is the form compared with $\mathrm{PR}(\infty)$ in Proposition 2.
--
--   **Formalization Note** "min, attained, equal to $V_{B(M)}$" is `IsLeast (H '' box) VB`: $V_{B(M)}$ is a value of $H$ on the box and is at most every such value.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 28, App. A, Proof of Proposition 1, (37)

import Mathlib
import Definitions.Def_L0BnB_BigMvsPR_Penalties
import Definitions.Def_L0BnB_BigMvsPR_Relaxations

namespace L0BnB.BigMvsPR

/-- (37), Proof of Proposition 1, p. 28: the interval relaxation of B(M) has optimal value
`min_{‖β‖_∞ ≤ M} L0BnB.Strength.H(β)`; the minimum over the L0BnB.Reduced.box is attained and equals `V_{B(M)}`. -/
theorem eq_37 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 lam2 M : ℝ)
    (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M) :
    IsLeast (L0BnB.Strength.H X y lam0 lam2 M '' L0BnB.Reduced.box p M) (L0BnB.Strength.VB X y lam0 lam2 M) := by sorry

end L0BnB.BigMvsPR
