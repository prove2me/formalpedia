-- Prove2me | Theorems.Thm_MultiPriceOnline_Ratios_two_price_formula
-- name    : MultiPriceOnline.Ratios.two_price_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:41:50.875871+00:00
-- url     : https://prove2.me/theorems/68fc1ff7-9569-47a3-9fb8-80235e382f3c
-- title:
--   (4), §1.3, p. 7 — for 𝒫 = {r, ξr}, F(𝒫) = 1 − (√(1 + 4ξ(ξ − 1)/e) − 1)/(2(ξ − 1)) and α⁽¹⁾ = ln(1/(1 − F(ξ)))
-- statement:
--   Let $\mathcal P = \{r, \xi r\}$ be a price set with two prices, $r > 0$ and $\xi > 1$, and let $\alpha^{(1)}, \alpha^{(2)}$ be its booking limits (positive, summing to $1$, satisfying (7)). Then
--   $$F(\mathcal P) = 1 - e^{-\alpha^{(1)}} = 1 - \frac{\sqrt{1 + 4\xi(\xi - 1)/e} - 1}{2(\xi - 1)} =: F(\xi), \qquad (4)$$
--   and the booking limit of the lower price is
--   $$\alpha^{(1)} = \ln\frac{1}{1 - F(\xi)}.$$
--
--   This is the paper's explicit two-price example; for $\xi = 3$ it is the price set $\{150, 450\}$ of the paper's Figure 1.
--
--   **Formalization Note** The price set is $r^{(1)} = r$, $r^{(2)} = \xi r$, and $e = \exp(1)$.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, p. 7, §1.3, (4)

import Mathlib
import Definitions.Def_MultiPriceOnline_Ratios_Setting

namespace MultiPriceOnline.Ratios

theorem two_price_formula (r : ℕ → ℝ) (ξ : ℝ) (hr1 : 0 < r 1) (hξ : 1 < ξ)
    (hr2 : r 2 = ξ * r 1) (α : ℕ → ℝ) (hα : MultiPriceOnline.Balance.IsBookingLimits 2 r α) :
    MultiPriceOnline.Ranking.F α = 1 - (Real.sqrt (1 + 4 * ξ * (ξ - 1) / Real.exp 1) - 1) / (2 * (ξ - 1)) ∧
    α 1 = Real.log (1 / (1 - (1 - (Real.sqrt (1 + 4 * ξ * (ξ - 1) / Real.exp 1) - 1) /
      (2 * (ξ - 1))))) := by sorry

end MultiPriceOnline.Ratios
