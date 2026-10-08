-- Prove2me | Theorems.Thm_L0BnB_Reduced_case_II
-- name    : L0BnB.Reduced.case_II
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:17:35.477971+00:00
-- url     : https://prove2.me/theorems/82eaac45-048b-4e2b-9d88-dc15c4a6958c
-- title:
--   Proof of Theorem 1, Case II — $\omega=(\lambda_0/M+\lambda_2M)|\beta_i|$ when $\sqrt{\lambda_0/\lambda_2}>M$
-- statement:
--   Fix $\lambda_0,\lambda_2,M>0$ with $\sqrt{\lambda_0/\lambda_2}>M$, and $b\in\mathbb R$ with $|b|\le M$. Let $\omega(b;\lambda_0,\lambda_2,M)$ be the minimum of $\lambda_0z+\lambda_2 s$ over the pairs $(z,s)$ with
--   $$b^2\le sz,\qquad -Mz\le b\le Mz,\qquad 0\le z\le 1,\qquad s\ge 0 .$$
--   Then this minimum is attained and equals
--   $$
--   \omega(b;\lambda_0,\lambda_2,M)=\Big(\frac{\lambda_0}{M}+\lambda_2M\Big)|b|=\psi_2(b;\lambda_0,\lambda_2,M).
--   $$
--
--   In this regime the Big-M constraint $|b|\le Mz$ is active at the optimum, and the ridge term of the perspective formulation turns into a pure $\ell_1$ penalty in the relaxation.
--
--   **Formalization Note** The statement is `IsLeast` of the set of values $\lambda_0z+\lambda_2s$ over the feasible pairs, so it asserts both attainment and the lower bound.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 28, App. A, Proof of Theorem 1, Case II

import Mathlib
import Definitions.Def_L0BnB_Reduced_ReverseHuber
import Definitions.Def_L0BnB_Reduced_Setup

namespace L0BnB.Reduced

/-- Proof of Theorem 1, Case II, p. 28: if `√(λ₀/λ₂) > M` and `|b| ≤ M`, then
`ω(b; λ₀, λ₂, M) = (λ₀/M + λ₂M)|b| = ψ₂(b; λ₀, λ₂, M)`. -/
theorem case_II (lam0 lam2 M b : ℝ) (h0 : 0 < lam0) (h2 : 0 < lam2) (hM : 0 < M)
    (hreg : M < Real.sqrt (lam0 / lam2)) (hb : |b| ≤ M) :
    IsLeast (omegaValues lam0 lam2 M b) (psi2 lam0 lam2 M b) := by sorry

end L0BnB.Reduced
