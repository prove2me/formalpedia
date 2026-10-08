-- Prove2me | Theorems.Thm_L0BnB_Strength_psi1_eq_on_box
-- name    : L0BnB.Strength.psi1_eq_on_box
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:29.877223+00:00
-- url     : https://prove2.me/theorems/951a2d73-f89a-48ee-a3e7-0c9125a5b21f
-- title:
--   Proof of Proposition 1, p. 29 — $\psi_1(b;\lambda_0,\lambda_2) = 2|b|\sqrt{\lambda_0\lambda_2}$ when $|b|\le M<\sqrt{\lambda_0/\lambda_2}$
-- statement:
--   Let $\lambda_0,\lambda_2>0$ and let $M$ satisfy $\sqrt{\lambda_0/\lambda_2} > M$. If $b\in\mathbb R$ satisfies $|b|\le M$, then
--
--   $$\psi_1(b;\lambda_0,\lambda_2) = 2|b|\sqrt{\lambda_0\lambda_2},$$
--
--   where $\psi_1(b;\lambda_0,\lambda_2) = 2\lambda_0\mathcal B(b\sqrt{\lambda_2/\lambda_0})$ and $\mathcal B$ is the reverse Huber penalty (4). This is the first, linear, case of (4): on the box the reverse Huber penalty reduces to a multiple of the absolute value.
--
--   The identity turns the difference between the penalties of the relaxations (5) and (6) into a multiple of $|b|$, coordinate by coordinate.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 29, App. A, Proof of Proposition 1

import Mathlib
import Definitions.Def_L0BnB_Strength_Penalties
import Definitions.Def_L0BnB_Strength_Relaxations

namespace L0BnB.Strength

/-- Proof of Proposition 1, p. 29: if `|b| ≤ M` and `√(λ₀/λ₂) > M`, then
`ψ₁(b; λ₀, λ₂) = 2 |b| √(λ₀ λ₂)` (the first case of (4)). -/
theorem psi1_eq_on_box (lam0 lam2 M b : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2)
    (hregime : M < Real.sqrt (lam0 / lam2)) (hb : |b| ≤ M) :
    L0BnB.Reduced.psi1 lam0 lam2 b = 2 * |b| * Real.sqrt (lam0 * lam2) := by sorry

end L0BnB.Strength
