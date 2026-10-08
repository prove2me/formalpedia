-- Prove2me | Theorems.Thm_L0BnB_Reduced_case_I
-- name    : L0BnB.Reduced.case_I
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:07.937798+00:00
-- url     : https://prove2.me/theorems/ea372633-1631-40b4-946c-ba8edffdef37
-- title:
--   Proof of Theorem 1, Case I — $\omega=2\lambda_0\mathcal B(\beta_i\sqrt{\lambda_2/\lambda_0})$ when $\sqrt{\lambda_0/\lambda_2}\le M$
-- statement:
--   Fix $\lambda_0,\lambda_2,M>0$ with $\sqrt{\lambda_0/\lambda_2}\le M$, and $b\in\mathbb R$ with $|b|\le M$. Let $\omega(b;\lambda_0,\lambda_2,M)$ be the minimum of $\lambda_0z+\lambda_2 s$ over the pairs $(z,s)$ with
--   $$b^2\le sz,\qquad -Mz\le b\le Mz,\qquad 0\le z\le 1,\qquad s\ge 0 .$$
--   Then this minimum is attained and equals
--   $$
--   \omega(b;\lambda_0,\lambda_2,M)=2\lambda_0\,\mathcal B\big(b\sqrt{\lambda_2/\lambda_0}\big)=\psi_1(b;\lambda_0,\lambda_2),
--   $$
--   where $\mathcal B$ is the reverse Huber penalty (4).
--
--   In this regime the Big-M bound does not bind the optimal $s$, and the relaxation of the perspective term produces the reverse Huber penalty: an $\ell_1$-type penalty $2\sqrt{\lambda_0\lambda_2}|b|$ for $|b|\le\sqrt{\lambda_0/\lambda_2}$ and $\lambda_0+\lambda_2b^2$ beyond.
--
--   **Formalization Note** The statement is `IsLeast` of the set of values $\lambda_0z+\lambda_2s$ over the feasible pairs, so it asserts both attainment and the lower bound.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 28, App. A, Proof of Theorem 1, Case I

import Mathlib
import Definitions.Def_L0BnB_Reduced_ReverseHuber
import Definitions.Def_L0BnB_Reduced_Setup

namespace L0BnB.Reduced

/-- Proof of Theorem 1, Case I, p. 28: if `√(λ₀/λ₂) ≤ M` and `|b| ≤ M`, then
`ω(b; λ₀, λ₂, M) = 2λ₀ B(b √(λ₂/λ₀)) = ψ₁(b; λ₀, λ₂)`. -/
theorem case_I (lam0 lam2 M b : ℝ) (h0 : 0 < lam0) (h2 : 0 < lam2) (hM : 0 < M)
    (hreg : Real.sqrt (lam0 / lam2) ≤ M) (hb : |b| ≤ M) :
    IsLeast (omegaValues lam0 lam2 M b) (psi1 lam0 lam2 b) := by sorry

end L0BnB.Reduced
