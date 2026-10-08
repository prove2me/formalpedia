-- Prove2me | Theorems.Thm_L0BnB_DualGap_eq_28
-- name    : L0BnB.DualGap.eq_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:29:20.017641+00:00
-- url     : https://prove2.me/theorems/253fa24a-5b1e-48d7-9e66-06aea4587331
-- title:
--   (28) — closed form of the dual feasible µ̂ of (27)
-- statement:
--   Let $X\in\mathbb R^{n\times p}$, $y\in\mathbb R^n$, $\lambda_0,\lambda_2,M>0$, $\hat\beta\in\mathbb R^p$ and $\hat\rho=-(y-X\hat\beta)$. If $\hat\mu$ maximizes $h_2(\hat\rho,\mu)=-\tfrac12\|\hat\rho\|_2^2-\hat\rho^\top y-M\|\mu\|_1$ over the $\mu\in\mathbb R^p$ with $|\hat\rho^\top X_i|-\mu_i\le\lambda_0/M+\lambda_2M$ for all $i$ (problem (27)), then for every $i\in[p]$
--   $$
--   \hat\mu_i=\big[\,|\hat\rho^\top X_i|-\lambda_0/M-\lambda_2M\,\big]_+ .\qquad(28)
--   $$
--
--   So the dual feasible solution of the $\ell_1$ regime is computable in closed form from the residual.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 14, (27), (28)

import Mathlib
import Definitions.Def_L0BnB_DualGap_Setup
import Definitions.Def_L0BnB_DualGap_Duals

namespace L0BnB.DualGap

/-- (28), p. 14: the maximizer `µ̂` of (27) is given in closed form by
`µ̂ᵢ = [|ρ̂ᵀXᵢ| − λ₀/M − λ₂M]₊`. -/
theorem eq_28 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (βhat μhat : Fin p → ℝ) (hμ : IsMuHat X y lam0 lam2 M βhat μhat) :
    ∀ i, μhat i = max (|colInner X (rhoHat X y βhat) i| - lam0 / M - lam2 * M) 0 := by sorry

end L0BnB.DualGap
