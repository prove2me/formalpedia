-- Prove2me | Theorems.Thm_MultiPriceOnline_Ratios_F_G_ranges
-- name    : MultiPriceOnline.Ratios.F_G_ranges
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:41:41.91109+00:00
-- url     : https://prove2.me/theorems/920d9abf-8929-4e29-b96e-6b1139372ecd
-- title:
--   §2.1, p. 14 — F(𝒫) ∈ [1 − e^{−1/m}, 1 − e^{−1}] and G(𝒫) ∈ [1/m, 1]
-- statement:
--   Let $m \ge 1$, let $0 < r^{(1)} < \dots < r^{(m)}$ be a price set, and let $\alpha^{(j)}$ and $\sigma^{(j)}$ be its booking limits (7) and Ball–Queyranne limits (8) (each positive and summing to $1$). Then
--   $$1 - e^{-1/m} \le F(\mathcal P) \le 1 - e^{-1}, \qquad \frac1m \le G(\mathcal P) \le 1,$$
--   where $F(\mathcal P) = 1 - e^{-\alpha^{(1)}}$ and $G(\mathcal P) = \sigma^{(1)}$.
--
--   These ranges show how the guarantees of the paper degrade with the number of prices: with one price ($m = 1$) the ratios are the classical $1 - 1/e$ and $1$, and in general they are bounded below in terms of $m$ alone.
--
--   **Formalization Note** "$F$ maps a price set to $[1 - e^{-1/m}, 1 - e^{-1}]$" is read as the two inequalities for every price set with $m$ prices; no claim that every value of the interval is attained is made.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, p. 14, §2.1, paragraph after Definition 2

import Mathlib
import Definitions.Def_MultiPriceOnline_Ratios_Setting

namespace MultiPriceOnline.Ratios

theorem F_G_ranges (m : ℕ) (hm : 1 ≤ m) (r : ℕ → ℝ) (hr : MultiPriceOnline.Balance.IsPriceSet m r)
    (α : ℕ → ℝ) (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) (σ : ℕ → ℝ) (hσ : MultiPriceOnline.Balance.IsBQLimits m r σ) :
    (1 - Real.exp (-(1 / (m : ℝ))) ≤ MultiPriceOnline.Ranking.F α ∧ MultiPriceOnline.Ranking.F α ≤ 1 - Real.exp (-1)) ∧
    (1 / (m : ℝ) ≤ G σ ∧ G σ ≤ 1) := by sorry

end MultiPriceOnline.Ratios
