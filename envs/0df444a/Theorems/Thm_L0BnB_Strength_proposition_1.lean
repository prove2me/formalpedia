-- Prove2me | Theorems.Thm_L0BnB_Strength_proposition_1
-- name    : L0BnB.Strength.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:40.696867+00:00
-- url     : https://prove2.me/theorems/cf96da42-bd15-44ef-9e66-935475c1aaa8
-- title:
--   Proposition 1 — for $\sqrt{\lambda_0/\lambda_2}>M$ the perspective relaxation dominates the Big-M and PR(∞) relaxations
-- statement:
--   Let $X\in\mathbb R^{n\times p}$, $y\in\mathbb R^n$, $\lambda_0,\lambda_2>0$ and $M>0$. Let $V_{PR(M)}$ be the optimal value of the reduced perspective relaxation (5),
--
--   $$V_{PR(M)} = \inf_{\|\beta\|_\infty\le M} F(\beta),\qquad F(\beta) = \tfrac12\|y-X\beta\|_2^2 + \sum_{i\in[p]}\psi(\beta_i;\lambda_0,\lambda_2,M),$$
--
--   let $V_{B(M)}$ be the optimal value of the interval relaxation of the Big-M formulation (2), and let $V_{PR(\infty)} = \inf_{\beta\in\mathbb R^p}G(\beta)$ with $G(\beta) = \tfrac12\|y-X\beta\|_2^2 + \sum_i \psi_1(\beta_i;\lambda_0,\lambda_2)$ as in (6). Let $\beta^*$ be an optimal solution to (5), and $h(\lambda_0,\lambda_2,M) = \lambda_0/M + \lambda_2M - 2\sqrt{\lambda_0\lambda_2}$. If $\sqrt{\lambda_0/\lambda_2} > M$, then
--
--   $$V_{PR(M)} \ge V_{B(M)} + \lambda_2\big(M\|\beta^*\|_1 - \|\beta^*\|_2^2\big), \tag{7}$$
--   $$V_{PR(M)} \ge V_{PR(\infty)} + h(\lambda_0,\lambda_2,M)\,\|\beta^*\|_1. \tag{8}$$
--
--   Both added terms are nonnegative in this regime, so the perspective relaxation is at least as tight as both the Big-M relaxation and $\mathrm{PR}(\infty)$, with explicit gaps that depend on the relaxation's own optimal solution. This is the theoretical basis for using $\mathrm{PR}(M)$ with a tight, valid $M$ in branch-and-bound.
--
--   **Formalization Note** $\beta^*$ is a binder with the hypotheses $\|\beta^*\|_\infty \le M$ and $F(\beta^*) \le F(\beta)$ for all feasible $\beta$. The regime is written $M < \sqrt{\lambda_0/\lambda_2}$.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 7, Proposition 1; App. A, Proof of Proposition 1, pp. 28–29

import Mathlib
import Definitions.Def_L0BnB_Strength_Penalties
import Definitions.Def_L0BnB_Strength_Relaxations

namespace L0BnB.Strength

/-- Proposition 1, p. 7: for `√(λ₀/λ₂) > M` and `β*` an optimal solution of (5),
`V_{PR(M)} ≥ V_{B(M)} + λ₂ (M ‖β*‖₁ − ‖β*‖₂²)` (7) and
`V_{PR(M)} ≥ V_{PR(∞)} + h(λ₀, λ₂, M) ‖β*‖₁` (8). -/
theorem proposition_1 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 lam2 M : ℝ)
    (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hregime : M < Real.sqrt (lam0 / lam2))
    (βs : Fin p → ℝ) (hβs_feas : ∀ i, |βs i| ≤ M)
    (hβs_opt : ∀ β : Fin p → ℝ, (∀ i, |β i| ≤ M) → L0BnB.Reduced.F X y lam0 lam2 M βs ≤ L0BnB.Reduced.F X y lam0 lam2 M β) :
    L0BnB.Reduced.VPR X y lam0 lam2 M ≥
        VB X y lam0 lam2 M + lam2 * (M * ∑ i, |βs i| - ∑ i, βs i ^ 2) ∧
      L0BnB.Reduced.VPR X y lam0 lam2 M ≥ VPRinf X y lam0 lam2 + hGap lam0 lam2 M * ∑ i, |βs i| := by sorry

end L0BnB.Strength
