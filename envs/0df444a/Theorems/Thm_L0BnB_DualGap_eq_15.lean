-- Prove2me | Theorems.Thm_L0BnB_DualGap_eq_15
-- name    : L0BnB.DualGap.eq_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:28:25.223489+00:00
-- url     : https://prove2.me/theorems/ff89e01f-c23b-4ec7-b299-9d715a23e394
-- title:
--   (15) — closed-form solution of the coordinate problem (13) when √(λ0/λ2) > M
-- statement:
--   Let $\lambda_0,\lambda_2,M>0$ with $\sqrt{\lambda_0/\lambda_2}>M$, so that the penalty is $\psi=\psi_2=(\lambda_0/M+\lambda_2M)|\cdot|$, and let $\tilde\beta_i\in\mathbb R$. Then the problem
--   $$
--   \min_{\beta_i\in\mathbb R}\ \tfrac12(\beta_i-\tilde\beta_i)^2+\psi(\beta_i;\lambda_0,\lambda_2,M)\quad\text{s.t.}\quad|\beta_i|\le M \qquad(13)
--   $$
--   has the unique solution
--   $$
--   \hat\beta_i=T\big(\tilde\beta_i;\,\lambda_0/M+\lambda_2M,\,M\big),
--   $$
--   where $T$ is the boxed soft-thresholding operator.
--
--   This is the closed-form coordinate-descent update in the $\ell_1$ regime.
--
--   **Formalization Note** "The solution" is stated as: the given value is feasible and every other feasible point has a strictly larger objective.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 10, (15); derivation in App. B.1, p. 34

import Mathlib
import Definitions.Def_L0BnB_DualGap_Setup

namespace L0BnB.DualGap

/-- (15), p. 10 (derivation App. B.1, p. 34): for `√(λ₀/λ₂) > M`, the solution of (13) is
`T(β̃ᵢ; λ₀/M + λ₂M, M)`. -/
theorem eq_15 (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hreg : M < Real.sqrt (lam0 / lam2)) (bt : ℝ) :
    IsSolution13 lam0 lam2 M bt (boxedSoftThreshold bt (lam0 / M + lam2 * M) M) := by sorry

end L0BnB.DualGap
