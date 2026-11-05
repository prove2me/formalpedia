-- Prove2me | Theorems.Thm_LiquidWelfareFPA_lambda2_expansion
-- name    : LiquidWelfareFPA.lambda2_expansion
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:32:37.640456+00:00
-- url     : https://prove2.me/theorems/457a2790-2a27-4146-905a-15224b4f260a
-- title:
--   Appendix A, p.22 — $1+1/\lambda_2=\gamma+1/2+O(1/\gamma)$
-- statement:
--   There is a constant $K\ge0$ such that for every $\gamma\ge1$
--
--   $$\Big|\,1+\frac1{\lambda_2(\gamma)}-\Big(\gamma+\frac12\Big)\Big|\ \le\ \frac K\gamma .$$
--
--   This is the expansion that gives the price-of-anarchy denominator $\gamma+1/2+O(1/\gamma)$ of Theorem 4.2.
--
--   Differences from the source:
--   - reading: 1 + 1/λ₂ = γ + 1/2 + O(1/γ) → ∃ K ≥ 0, ∀ γ ≥ 1, |1 + 1/λ₂ − (γ + 1/2)| ≤ K/γ; reason: the two-sided bound uniform on the whole range γ ≥ 1 of Theorem 4.2 is the strongest reading of O(1/γ)
-- source:
--   Fikioris & Tardos, Liquid Welfare Guarantees for No-Regret Learning in Sequential Budgeted Auctions, arXiv:2210.07502v4, Appendix A, p.22

import Mathlib
import Definitions.Def_LiquidWelfareFPA_lam2

namespace LiquidWelfareFPA

/-- **`1 + 1/λ₂ = γ + 1/2 + O(1/γ)`.**
Fikioris & Tardos, arXiv:2210.07502v4, Appendix A, p.22: "We now point out that
1 + 1/λ2 = γ + 1/2 + O(1/γ). One can verify that this is the case using Mathematica."

There is a constant `K ≥ 0` such that for every `γ ≥ 1`,
`|1 + 1/λ₂(γ) − (γ + 1/2)| ≤ K/γ`.

**Formalization Note** `O(1/γ)` is read as a two-sided bound uniform on all of `[1, ∞)`, the range
of `γ` in Theorem 4.2. -/
theorem lambda2_expansion :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ γ : ℝ, 1 ≤ γ → |1 + 1 / lam2 γ - (γ + 1 / 2)| ≤ K / γ := by sorry

end LiquidWelfareFPA
