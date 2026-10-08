-- Prove2me | Theorems.Thm_L0BnB_DualGap_eq_58
-- name    : L0BnB.DualGap.eq_58
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:30:03.033805+00:00
-- url     : https://prove2.me/theorems/7048097f-19a4-409d-9a6c-b20eeb6eeffd
-- title:
--   (58) — correlation conditions at an optimal β∗ when √(λ0/λ2) > M
-- statement:
--   Let $X\in\mathbb R^{n\times p}$, $y\in\mathbb R^n$, $\lambda_0,\lambda_2,M>0$ with $\sqrt{\lambda_0/\lambda_2}>M$, and let $\beta^*$ be an optimal solution of (5), $r^*=y-X\beta^*$ and $\rho^*=-r^*$. Then for every $i\in[p]$
--   $$
--   |\rho^{*\top}X_i|\le\lambda_0/M+\lambda_2M\ \text{ if } |\beta^*_i|<M\qquad\text{and}\qquad |\rho^{*\top}X_i|\ge\lambda_0/M+\lambda_2M\ \text{ if } |\beta^*_i|=M.\qquad(58)
--   $$
--
--   These conditions identify $|\mu^*_i|$ with $[|\rho^{*\top}X_i|-\lambda_0/M-\lambda_2M]_+$, which is the step from (57) to the dual bound (30).
--
--   **Formalization Note** The paper derives (58) from the optimality of $(\rho^*,\mu^*)$ for the dual (22) (Theorem 2). Here the hypothesis is the optimality of $\beta^*$ for the primal (5); Theorem 2 is not assumed. No normalization of $X$ or $y$ is needed.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 34, (58), Proof of Theorem 3

import Mathlib
import Definitions.Def_L0BnB_DualGap_Setup
import Definitions.Def_L0BnB_DualGap_Duals

namespace L0BnB.DualGap

/-- (58), p. 34: for `√(λ₀/λ₂) > M` and `β*` optimal for (5), with `ρ* = −r*`:
`|ρ*ᵀXᵢ| ≤ λ₀/M + λ₂M` if `|β*ᵢ| < M` and `|ρ*ᵀXᵢ| ≥ λ₀/M + λ₂M` if `|β*ᵢ| = M`. -/
theorem eq_58 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hreg : M < Real.sqrt (lam0 / lam2))
    (βs : Fin p → ℝ) (hβs : IsOptimal X y lam0 lam2 M βs) :
    ∀ i, (|βs i| < M → |colInner X (L0BnB.Duality.rhoStar X y βs) i| ≤ lam0 / M + lam2 * M) ∧
      (|βs i| = M → lam0 / M + lam2 * M ≤ |colInner X (L0BnB.Duality.rhoStar X y βs) i|) := by sorry

end L0BnB.DualGap
