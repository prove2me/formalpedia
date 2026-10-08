-- Prove2me | Theorems.Thm_L0BnB_Strength_ineq_7
-- name    : L0BnB.Strength.ineq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:44.053562+00:00
-- url     : https://prove2.me/theorems/d68fb855-9d50-4e1c-8eea-c3fa16b69948
-- title:
--   (7) — for $\sqrt{\lambda_0/\lambda_2}>M$, $V_{PR(M)} \ge V_{B(M)} + \lambda_2(M\|\beta^*\|_1 - \|\beta^*\|_2^2)$
-- statement:
--   Let $X\in\mathbb R^{n\times p}$, $y\in\mathbb R^n$, $\lambda_0,\lambda_2>0$ and $M>0$ with $\sqrt{\lambda_0/\lambda_2} > M$. Let $V_{PR(M)}$ be the optimal value of the reduced perspective relaxation (5), $V_{B(M)}$ that of the interval relaxation of the Big-M formulation (2), and let $\beta^*$ be an optimal solution of (5): $\|\beta^*\|_\infty\le M$ and $F(\beta^*) \le F(\beta)$ for every $\beta$ with $\|\beta\|_\infty\le M$. Then
--
--   $$V_{PR(M)} \ge V_{B(M)} + \lambda_2\big(M\|\beta^*\|_1 - \|\beta^*\|_2^2\big).$$
--
--   Since $\|\beta^*\|_\infty \le M$, the added term is nonnegative, and it is positive as soon as some coordinate satisfies $0<|\beta^*_i|<M$: in this regime the perspective relaxation is at least as strong as the Big-M relaxation, with a quantified gap.
--
--   **Formalization Note** $\|\beta^*\|_1 = \sum_i|\beta^*_i|$ and $\|\beta^*\|_2^2 = \sum_i(\beta^*_i)^2$ are explicit sums. The optimal solution $\beta^*$ is a hypothesis-carrying binder, not a chosen minimizer.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 7, Proposition 1, (7); proof p. 28

import Mathlib
import Definitions.Def_L0BnB_Strength_Penalties
import Definitions.Def_L0BnB_Strength_Relaxations

namespace L0BnB.Strength

/-- (7), Proposition 1, p. 7 (proof p. 28): for `√(λ₀/λ₂) > M` and `β*` an optimal solution of (5),
`V_{PR(M)} ≥ V_{B(M)} + λ₂ (M ‖β*‖₁ − ‖β*‖₂²)`. -/
theorem ineq_7 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 lam2 M : ℝ)
    (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hregime : M < Real.sqrt (lam0 / lam2))
    (βs : Fin p → ℝ) (hβs_feas : ∀ i, |βs i| ≤ M)
    (hβs_opt : ∀ β : Fin p → ℝ, (∀ i, |β i| ≤ M) → L0BnB.Reduced.F X y lam0 lam2 M βs ≤ L0BnB.Reduced.F X y lam0 lam2 M β) :
    L0BnB.Reduced.VPR X y lam0 lam2 M ≥
      VB X y lam0 lam2 M + lam2 * (M * ∑ i, |βs i| - ∑ i, βs i ^ 2) := by sorry

end L0BnB.Strength
