-- Prove2me | Theorems.Thm_MultiPriceOnline_Hardness_eq_35
-- name    : MultiPriceOnline.Hardness.eq_35
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:16.943522+00:00
-- url     : https://prove2.me/theorems/5d99bdac-47b8-401d-8e32-51613bd95709
-- title:
--   (35), App. B, p. 39 — r⁽ʲ⁻¹⁾/r⁽ʲ⁾ ≤ e^{−α⁽ʲ⁾}
-- statement:
--   Let $0 < r^{(1)} < \dots < r^{(m)}$ be a price set and let $\alpha^{(1)}, \dots, \alpha^{(m)}$ be its booking limits from Proposition 1, so that (7) holds. Then for every $j = 2, \dots, m$,
--
--   $$\frac{r^{(j-1)}}{r^{(j)}} \le e^{-\alpha^{(j)}}.$$
--
--   The inequality compares consecutive prices with the booking limits. It is used in the proof of Proposition 4 to show that $B_j < B_{j-1}$.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, p. 39, App. B, eq. (35)

import Mathlib
import Definitions.Def_MultiPriceOnline_Hardness_PriceSet

namespace MultiPriceOnline.Hardness
theorem eq_35 {m : ℕ} {r α : ℕ → ℝ} (hr : MultiPriceOnline.Balance.IsPriceSet m r) (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) :
    ∀ j : ℕ, 2 ≤ j → j ≤ m → r (j - 1) / r j ≤ Real.exp (-α j) := by sorry
end MultiPriceOnline.Hardness
