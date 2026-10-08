-- Prove2me | Theorems.Thm_L0BnB_DualGap_ineq_53
-- name    : L0BnB.DualGap.ineq_53
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:30:45.562883+00:00
-- url     : https://prove2.me/theorems/155a27ad-ae7b-49a4-9e26-480ad560dae5
-- title:
--   (53) — the quadratic part of h1 at α̂ exceeds that at α∗ by at most ½ϵ² + 2ϵ
-- statement:
--   Let $X\in\mathbb R^{n\times p}$, $y\in\mathbb R^n$ with $\|y\|_2=1$, $\lambda_0,\lambda_2,M>0$, $\beta^*$ an optimal solution of (5) and $\hat\beta\in\mathbb R^p$. With $\alpha^*=-(y-X\beta^*)$, $\hat\alpha=-(y-X\hat\beta)$ and $\epsilon=\|X(\beta^*-\hat\beta)\|_2$,
--   $$
--   \tfrac12\|\hat\alpha\|_2^2+\hat\alpha^\top y\le\tfrac12\epsilon^2+2\epsilon+\tfrac12\|\alpha^*\|_2^2+\alpha^{*\top}y.\qquad(53)
--   $$
--
--   This compares the smooth part of the dual objective $h_1$ at the constructed and the optimal dual points; together with Lemma 2 it gives the dual-bound guarantee.
--
--   **Formalization Note** The inequality holds for every $\hat\beta$; the paper applies it to the output of Algorithm 2, and no property of that output is used. It also does not depend on the regime of $\sqrt{\lambda_0/\lambda_2}$ versus $M$.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 33, Proof of Theorem 3, (53) (from (52), p. 32)

import Mathlib
import Definitions.Def_L0BnB_DualGap_Setup
import Definitions.Def_L0BnB_DualGap_Duals

namespace L0BnB.DualGap

/-- (53), Proof of Theorem 3, p. 33: with `‖y‖₂ = 1`, `β*` optimal for (5), `α* = −r*`, `α̂ = −r̂`
and `ϵ = ‖X(β* − β̂)‖₂`: `½‖α̂‖₂² + α̂ᵀy ≤ ½ϵ² + 2ϵ + ½‖α*‖₂² + α*ᵀy`. -/
theorem ineq_53 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hy : ∑ r, y r ^ 2 = 1) (βs : Fin p → ℝ) (hβs : IsOptimal X y lam0 lam2 M βs)
    (βhat : Fin p → ℝ) :
    (1 / 2) * ∑ r, alphaHat X y βhat r ^ 2 + ∑ r, alphaHat X y βhat r * y r ≤
      (1 / 2) * primalGap X βs βhat ^ 2 + 2 * primalGap X βs βhat
        + (1 / 2) * ∑ r, L0BnB.Duality.alphaStar X y βs r ^ 2 + ∑ r, L0BnB.Duality.alphaStar X y βs r * y r := by sorry

end L0BnB.DualGap
