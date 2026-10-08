-- Prove2me | Theorems.Thm_L0BnB_BigMvsPR_ineq_10
-- name    : L0BnB.BigMvsPR.ineq_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:28:49.427307+00:00
-- url     : https://prove2.me/theorems/650a29ad-8278-4e6d-9e78-3cd77d03e57f
-- title:
--   (10) — $V_{B(M)} \ge V_{PR(\infty)}$ for $M \le \frac12\sqrt{\lambda_0/\lambda_2}$
-- statement:
--   Let $X \in \mathbb R^{n\times p}$, $y \in \mathbb R^n$ and $\lambda_0, \lambda_2, M > 0$. Let $V_{B(M)}$ be the optimal value of the interval relaxation of the Big-M formulation (2), and $V_{PR(\infty)} = \min_{\beta\in\mathbb R^p} G(\beta)$ the value (6) of the interval relaxation of $\mathrm{PR}(\infty)$. If $M \le \frac12\sqrt{\lambda_0/\lambda_2}$, then
--
--   $$V_{B(M)} \ge V_{PR(\infty)}.$$
--
--   So for a sufficiently tight Big-M bound, the Big-M relaxation gives a lower bound at least as large as that of the perspective relaxation without box constraint. This is the first half of Proposition 2.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 7, Proposition 2, (10); proof p. 29, (40)

import Mathlib
import Definitions.Def_L0BnB_BigMvsPR_Penalties
import Definitions.Def_L0BnB_BigMvsPR_Relaxations

namespace L0BnB.BigMvsPR

/-- (10) of Proposition 2, p. 7 (proof (40), p. 29): if `M ≤ ½ √(λ₀/λ₂)` then
`V_{B(M)} ≥ V_{PR(∞)}`. -/
theorem ineq_10 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 lam2 M : ℝ)
    (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hMsmall : M ≤ (1 / 2) * Real.sqrt (lam0 / lam2)) :
    L0BnB.Strength.VPRinf X y lam0 lam2 ≤ L0BnB.Strength.VB X y lam0 lam2 M := by sorry

end L0BnB.BigMvsPR
