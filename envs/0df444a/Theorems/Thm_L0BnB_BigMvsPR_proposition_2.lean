-- Prove2me | Theorems.Thm_L0BnB_BigMvsPR_proposition_2
-- name    : L0BnB.BigMvsPR.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:28:55.413666+00:00
-- url     : https://prove2.me/theorems/d1c347b8-c74a-4016-a8bf-e93b4667cc4d
-- title:
--   Proposition 2 — $V_{B(M)} \ge V_{PR(\infty)}$ if $M \le \frac12\sqrt{\lambda_0/\lambda_2}$; $V_{B(M)} \le V_{PR(\infty)}$ if $M \ge \sqrt{\lambda_0/\lambda_2}$ and $\lambda_2 \in \mathcal L(M)$
-- statement:
--   Let $X \in \mathbb R^{n\times p}$, $y \in \mathbb R^n$ and $\lambda_0, \lambda_2, M > 0$. Let $V_{B(M)}$ be the optimal value of the interval relaxation of the Big-M formulation (2) of $\ell_0\ell_2$-regularized least squares, and
--
--   $$V_{PR(\infty)} = \min_{\beta\in\mathbb R^p}\ \tfrac12\|y - X\beta\|_2^2 + \sum_{i\in[p]} 2\lambda_0\,\mathcal B\big(\beta_i\sqrt{\lambda_2/\lambda_0}\big)$$
--
--   the value (6) of the interval relaxation of the perspective formulation $\mathrm{PR}(\infty)$, where $\mathcal B$ is the reverse Huber penalty (4). Let $\mathcal S(\lambda_2)$ be the set of minimizers in (6) and $\mathcal L(M) = \{\lambda_2 > 0 : \exists\beta\in\mathcal S(\lambda_2),\ \|\beta\|_\infty \le M\}$ as in (9). Then:
--
--   1. if $M \le \frac12\sqrt{\lambda_0/\lambda_2}$, then $$V_{B(M)} \ge V_{PR(\infty)};\qquad (10)$$
--   2. if $M \ge \sqrt{\lambda_0/\lambda_2}$ and $\lambda_2 \in \mathcal L(M)$, then $$V_{B(M)} \le V_{PR(\infty)}.\qquad (11)$$
--
--   Neither relaxation dominates the other in general: a tight Big-M bound makes the Big-M relaxation the stronger one, while a loose one makes it the weaker one, provided some optimal solution of $\mathrm{PR}(\infty)$ lies in the box.
--
--   **Formalization Note** Optimal values are real infima (`sInf`), well defined because the objectives are nonnegative and the feasible sets nonempty. The paper remarks (p. 8) that the proposition applies for any $M \ge 0$; the statement here assumes $M > 0$, since the function $t$ and the reformulation (37) divide by $M$; at $M = 0$ the hypothesis of (11) cannot hold.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 7, Proposition 2, (9)–(11); proof pp. 29–30

import Mathlib
import Definitions.Def_L0BnB_BigMvsPR_Penalties
import Definitions.Def_L0BnB_BigMvsPR_Relaxations

namespace L0BnB.BigMvsPR

/-- Proposition 2, p. 7: with `L(M)` as in (9),
(10) `V_{B(M)} ≥ V_{PR(∞)}` if `M ≤ ½ √(λ₀/λ₂)`, and
(11) `V_{B(M)} ≤ V_{PR(∞)}` if `M ≥ √(λ₀/λ₂)` and `λ₂ ∈ L(M)`. -/
theorem proposition_2 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 lam2 M : ℝ)
    (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M) :
    (M ≤ (1 / 2) * Real.sqrt (lam0 / lam2) → L0BnB.Strength.VPRinf X y lam0 lam2 ≤ L0BnB.Strength.VB X y lam0 lam2 M) ∧
      (Real.sqrt (lam0 / lam2) ≤ M → lam2 ∈ L X y lam0 M →
        L0BnB.Strength.VB X y lam0 lam2 M ≤ L0BnB.Strength.VPRinf X y lam0 lam2) := by sorry

end L0BnB.BigMvsPR
