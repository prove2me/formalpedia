-- Prove2me | Theorems.Thm_L0BnB_DualGap_ineq_57
-- name    : L0BnB.DualGap.ineq_57
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:29:19.744448+00:00
-- url     : https://prove2.me/theorems/d4871711-a893-4e1e-acce-624bf9b66718
-- title:
--   (57) — |µ̂i| ≤ ϵ + |µ∗i| on the support of β̂
-- statement:
--   Assume $\sqrt{\lambda_0/\lambda_2}>M$ (with $\lambda_0,\lambda_2,M>0$) and that every column of $X\in\mathbb R^{n\times p}$ has unit $\ell_2$ norm; let $y\in\mathbb R^n$. Let $\beta^*$ be an optimal solution of (5), $\rho^*=-(y-X\beta^*)$ and $\mu^*$ as in (24). Let $\hat\beta\in\mathbb R^p$, $\hat\rho=-(y-X\hat\beta)$, $\hat\mu$ a maximizer of (27), and $\epsilon=\|X(\beta^*-\hat\beta)\|_2$. Then for every $i\in\operatorname{Supp}(\hat\beta)$
--   $$
--   |\hat\mu_i|\le\epsilon+|\mu^*_i| .\qquad(57)
--   $$
--
--   This is the per-coordinate step of the bound (30): the loss on the support is at most $\epsilon$ per coordinate.
--
--   **Formalization Note** $\mu^*$ is the formula (24); its optimality (Theorem 2) is not assumed. The unit norm of $y$ is not needed and is not assumed.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 33, Proof of Theorem 3, (57)

import Mathlib
import Definitions.Def_L0BnB_DualGap_Setup
import Definitions.Def_L0BnB_DualGap_Duals

namespace L0BnB.DualGap

/-- (57), Proof of Theorem 3, p. 33: for `√(λ₀/λ₂) > M`, unit-norm columns of `X`, `β*` optimal for
(5), `µ̂` as in (27) and `i ∈ Supp(β̂)`: `|µ̂ᵢ| ≤ ϵ + |µ*ᵢ|`, with `ϵ = ‖X(β* − β̂)‖₂`. -/
theorem ineq_57 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hreg : M < Real.sqrt (lam0 / lam2)) (hX : ∀ i, ∑ r, X r i ^ 2 = 1)
    (βs : Fin p → ℝ) (hβs : IsOptimal X y lam0 lam2 M βs)
    (βhat μhat : Fin p → ℝ) (hμ : IsMuHat X y lam0 lam2 M βhat μhat)
    (i : Fin p) (hi : βhat i ≠ 0) :
    |μhat i| ≤ primalGap X βs βhat + |L0BnB.Duality.muStar X y lam0 lam2 M βs i| := by sorry

end L0BnB.DualGap
