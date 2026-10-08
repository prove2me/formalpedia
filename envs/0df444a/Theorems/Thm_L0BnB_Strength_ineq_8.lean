-- Prove2me | Theorems.Thm_L0BnB_Strength_ineq_8
-- name    : L0BnB.Strength.ineq_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:47.49033+00:00
-- url     : https://prove2.me/theorems/f46c436c-8782-4b1c-a91e-2c03716cb621
-- title:
--   (8) — for $\sqrt{\lambda_0/\lambda_2}>M$, $V_{PR(M)} \ge V_{PR(\infty)} + h(\lambda_0,\lambda_2,M)\|\beta^*\|_1$
-- statement:
--   Let $X\in\mathbb R^{n\times p}$, $y\in\mathbb R^n$, $\lambda_0,\lambda_2>0$ and $M>0$ with $\sqrt{\lambda_0/\lambda_2} > M$. Let $V_{PR(M)}$ be the optimal value of the reduced perspective relaxation (5), $V_{PR(\infty)} = \inf_{\beta\in\mathbb R^p} G(\beta)$ the value (6), and $\beta^*$ an optimal solution of (5). With $h(\lambda_0,\lambda_2,M) = \lambda_0/M + \lambda_2M - 2\sqrt{\lambda_0\lambda_2}$,
--
--   $$V_{PR(M)} \ge V_{PR(\infty)} + h(\lambda_0,\lambda_2,M)\,\|\beta^*\|_1.$$
--
--   For $\sqrt{\lambda_0/\lambda_2} > M$ the factor $h$ is strictly positive, so the perspective relaxation with a finite bound $M$ is strictly stronger than $\mathrm{PR}(\infty)$ whenever $\beta^*\ne 0$.
--
--   **Formalization Note** $V_{PR(\infty)}$ is (6) as printed (the infimum of $G$ over $\mathbb R^p$); see the definition item.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 7, Proposition 1, (8); proof p. 29, (38)

import Mathlib
import Definitions.Def_L0BnB_Strength_Penalties
import Definitions.Def_L0BnB_Strength_Relaxations

namespace L0BnB.Strength

/-- (8), Proposition 1, p. 7 (proof (38), p. 29): for `√(λ₀/λ₂) > M` and `β*` an optimal solution
of (5), `V_{PR(M)} ≥ V_{PR(∞)} + h(λ₀, λ₂, M) ‖β*‖₁`. -/
theorem ineq_8 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 lam2 M : ℝ)
    (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hregime : M < Real.sqrt (lam0 / lam2))
    (βs : Fin p → ℝ) (hβs_feas : ∀ i, |βs i| ≤ M)
    (hβs_opt : ∀ β : Fin p → ℝ, (∀ i, |β i| ≤ M) → L0BnB.Reduced.F X y lam0 lam2 M βs ≤ L0BnB.Reduced.F X y lam0 lam2 M β) :
    L0BnB.Reduced.VPR X y lam0 lam2 M ≥ VPRinf X y lam0 lam2 + hGap lam0 lam2 M * ∑ i, |βs i| := by sorry

end L0BnB.Strength
