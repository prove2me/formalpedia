-- Prove2me | Theorems.Thm_L0BnB_Duality_eq_47
-- name    : L0BnB.Duality.eq_47
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:58.573562+00:00
-- url     : https://prove2.me/theorems/371d47d5-f091-4c11-bb63-ab18fc5d4677
-- title:
--   (47) — the minimum of $D_i$ when $|\alpha^TX_i|-\eta_i\ge 2\sqrt{\lambda_0\lambda_2}$
-- statement:
--   Let $\lambda_0,\lambda_2>0$, let $a\in\mathbb R$ (standing for $\alpha^TX_i$) and $\eta\ge 0$, and let $D(b)=\psi_1(b;\lambda_0,\lambda_2)+ab+\eta|b|$ for $b\in\mathbb R$. If $|a|-\eta\ge 2\sqrt{\lambda_0\lambda_2}$, then the minimum of $D$ over $\mathbb R$ is attained and
--
--   $$
--   \min_{b\in\mathbb R} D(b) = -\frac{1}{4\lambda_2}\big(|a|-\eta\big)^2+\lambda_0 .
--   $$
--
--   This is the value of the inner minimization of the Lagrangian in the proof of Theorem 2 when the correlation $|\alpha^TX_i|$ is large; together with (45) it gives the closed form of the dual function.
--
--   **Formalization Note** "min" is stated as `IsLeast` of the range of $D$, so attainment is part of the statement. The paper's subsequent combined formula $-[(|a|-\eta)^2/(4\lambda_2)-\lambda_0]_+$ is not stated: it fails when $\eta>|a|+2\sqrt{\lambda_0\lambda_2}$.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 31, Proof of Theorem 2, Case 2, (47)

import Mathlib
import Definitions.Def_L0BnB_Duality_Dual

namespace L0BnB.Duality

/-- (47), proof of Theorem 2, p. 31. For `a = αᵀXᵢ` and `η = ηᵢ ≥ 0` with
`|a| − η ≥ 2√(λ₀λ₂)`, the minimum over `βᵢ ∈ ℝ` of `Dᵢ(βᵢ) = ψ₁(βᵢ; λ₀, λ₂) + a βᵢ + η|βᵢ|`
is attained and equals `−(|a| − η)²/(4λ₂) + λ₀`. -/
theorem eq_47 (lam0 lam2 a η : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hη : 0 ≤ η)
    (hcase : |a| - η ≥ 2 * Real.sqrt (lam0 * lam2)) :
    IsLeast (Set.range (D lam0 lam2 a η)) (-(1 / (4 * lam2)) * (|a| - η) ^ 2 + lam0) := by sorry

end L0BnB.Duality
