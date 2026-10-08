-- Prove2me | Theorems.Thm_L0BnB_DualGap_ineq_56
-- name    : L0BnB.DualGap.ineq_56
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:29:27.944912+00:00
-- url     : https://prove2.me/theorems/3e720608-94b5-4f8a-8db7-8e0ea3bb22d0
-- title:
--   (56) — lower bound on h2(ρ̂, µ̂) in terms of ρ∗, ϵ and ‖µ̂‖1
-- statement:
--   Let $X\in\mathbb R^{n\times p}$, $y\in\mathbb R^n$ with $\|y\|_2=1$, $\lambda_0,\lambda_2,M>0$, $\beta^*$ an optimal solution of (5), $\rho^*=-(y-X\beta^*)$, $\hat\beta\in\mathbb R^p$, $\hat\rho=-(y-X\hat\beta)$, $\hat\mu\in\mathbb R^p$ and $\epsilon=\|X(\beta^*-\hat\beta)\|_2$. Then
--   $$
--   h_2(\hat\rho,\hat\mu)\ge-\tfrac12\|\rho^*\|_2^2-\rho^{*\top}y-2\epsilon-\tfrac12\epsilon^2-M\|\hat\mu\|_1 .\qquad(56)
--   $$
--
--   It is the $\ell_1$-regime counterpart of (54), obtained by the argument of (53).
--
--   **Formalization Note** The inequality holds for every $\hat\beta$ and every $\hat\mu$; the paper applies it to the output of Algorithm 2 and the maximizer (27), and no property of them is used. It does not depend on the regime of $\sqrt{\lambda_0/\lambda_2}$ versus $M$.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 33, Proof of Theorem 3, (56)

import Mathlib
import Definitions.Def_L0BnB_DualGap_Setup
import Definitions.Def_L0BnB_DualGap_Duals

namespace L0BnB.DualGap

/-- (56), Proof of Theorem 3, p. 33: with `‖y‖₂ = 1`, `β*` optimal for (5), `ρ* = −r*`, `ρ̂ = −r̂`
and `ϵ = ‖X(β* − β̂)‖₂`: `h₂(ρ̂, µ̂) ≥ −½‖ρ*‖₂² − ρ*ᵀy − 2ϵ − ½ϵ² − M‖µ̂‖₁`. -/
theorem ineq_56 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hy : ∑ r, y r ^ 2 = 1) (βs : Fin p → ℝ) (hβs : IsOptimal X y lam0 lam2 M βs)
    (βhat μhat : Fin p → ℝ) :
    -(1 / 2) * ∑ r, L0BnB.Duality.rhoStar X y βs r ^ 2 - ∑ r, L0BnB.Duality.rhoStar X y βs r * y r
        - 2 * primalGap X βs βhat - (1 / 2) * primalGap X βs βhat ^ 2 - M * ∑ i, |μhat i|
      ≤ L0BnB.Duality.h2 y M (rhoHat X y βhat) μhat := by sorry

end L0BnB.DualGap
