-- Prove2me | Theorems.Thm_MultiPriceOnline_Balance_eq_35
-- name    : MultiPriceOnline.Balance.eq_35
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:43:30.624628+00:00
-- url     : https://prove2.me/theorems/1cdef08f-8058-4927-bcfe-958c2b4910db
-- title:
--   (35), App. B, p. 39 — r⁽ʲ⁻¹⁾/r⁽ʲ⁾ ≤ e^{−α⁽ʲ⁾} for booking limits
-- statement:
--   Let $0<r^{(1)}<\dots<r^{(m)}$ be a price set and $\alpha^{(1)},\dots,\alpha^{(m)}$ its booking limits: positive, summing to $1$, and satisfying (7). Then for every $j=2,\dots,m$,
--   $$
--   \frac{r^{(j-1)}}{r^{(j)}}\le e^{-\alpha^{(j)}}.\tag{35}
--   $$
--
--   The paper calls this inequality "useful throughout"; it bounds the booking limit of each higher price by the relative price increment.
--
--   **Formalization Note** The same statement is posed in mission III of this series (the upper bound), because drafts of concurrent missions cannot import each other.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, App. B, p. 39, (35)

import Mathlib
import Definitions.Def_MultiPriceOnline_Balance_PriceSet

namespace MultiPriceOnline.Balance

/-- Inequality (35) (Ma–Simchi-Levi, arXiv:1905.04770v1, App. B, p. 39): for booking limits `α`
of a price set `0 < r⁽¹⁾ < … < r⁽ᵐ⁾`, `r⁽ʲ⁻¹⁾/r⁽ʲ⁾ ≤ e^{−α⁽ʲ⁾}` for all `j = 2, …, m`. -/
theorem eq_35 (m : ℕ) (r α : ℕ → ℝ) (hr : IsPriceSet m r) (hα : IsBookingLimits m r α) :
    ∀ j, 2 ≤ j → j ≤ m → r (j - 1) / r j ≤ Real.exp (-α j) := by sorry

end MultiPriceOnline.Balance
