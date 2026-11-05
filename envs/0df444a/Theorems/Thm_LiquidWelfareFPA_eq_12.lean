-- Prove2me | Theorems.Thm_LiquidWelfareFPA_eq_12
-- name    : LiquidWelfareFPA.eq_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:32:47.453222+00:00
-- url     : https://prove2.me/theorems/0b1c9de4-d55b-4c6f-ab1b-eba6346db4f6
-- title:
--   Appendix A, (12), p.22 — $1+1/\lambda_2\ge\gamma\lambda_2/(1-\lambda_2)$ for $\gamma\ge\gamma_0$
-- statement:
--   For every $\gamma\ge\gamma_0$ ($\gamma_0\approx1.725$ the threshold),
--
--   $$1+\frac1{\lambda_2}\ \ge\ \frac{\gamma\lambda_2}{1-\lambda_2}.$$
--
--   With the equation $1+1/\lambda_2=\gamma/(c(\lambda_2)\lambda_2)$ this shows that for $\gamma\ge\gamma_0$ the maximum in the aggregated inequality at $\lambda=\lambda_2$ is $1+1/\lambda_2$.
--
--   Differences from the source: none.
-- source:
--   Fikioris & Tardos, Liquid Welfare Guarantees for No-Regret Learning in Sequential Budgeted Auctions, arXiv:2210.07502v4, Appendix A, (12), p.22

import Mathlib
import Definitions.Def_LiquidWelfareFPA_lam2
import Definitions.Def_LiquidWelfareFPA_gamma0

namespace LiquidWelfareFPA

/-- **Inequality (12): `1 + 1/λ₂ ≥ γλ₂/(1−λ₂)` for `γ ≥ γ₀`.**
Fikioris & Tardos, arXiv:2210.07502v4, Appendix A, (12), p.22: "We now prove that for γ ≥ γ0 it
holds that 1 + 1/λ2 ≥ γλ2/(1 − λ2)".

For every `γ ≥ γ₀` (`γ₀ = gamma0 ≈ 1.725`), `γλ₂/(1−λ₂) ≤ 1 + 1/λ₂`. -/
theorem eq_12 (γ : ℝ) (hγ : gamma0 ≤ γ) :
    γ * lam2 γ / (1 - lam2 γ) ≤ 1 + 1 / lam2 γ := by sorry

end LiquidWelfareFPA
