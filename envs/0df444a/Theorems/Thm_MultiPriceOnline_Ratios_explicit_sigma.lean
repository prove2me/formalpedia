-- Prove2me | Theorems.Thm_MultiPriceOnline_Ratios_explicit_sigma
-- name    : MultiPriceOnline.Ratios.explicit_sigma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:41:17.148977+00:00
-- url     : https://prove2.me/theorems/d2656818-75a9-483d-8fa3-a5f73cc91d1b
-- title:
--   App. A, p. 38 — explicit Ball–Queyranne limits σ⁽ʲ⁾ = (1 − r⁽ʲ⁻¹⁾/r⁽ʲ⁾)(1 + Σⱼ′ (1 − r⁽ʲ′⁻¹⁾/r⁽ʲ′⁾))⁻¹
-- statement:
--   Let $m \ge 1$, let $0 < r^{(1)} < \dots < r^{(m)}$ be a price set with $r^{(0)} := 0$, and let $\sigma^{(1)}, \dots, \sigma^{(m)}$ be positive, sum to $1$ and satisfy (8). Then for every $j \in \{1, \dots, m\}$,
--   $$\sigma^{(j)} = \Bigl(1 - \frac{r^{(j-1)}}{r^{(j)}}\Bigr)\Bigl(1 + \sum_{j'=2}^{m} \Bigl(1 - \frac{r^{(j'-1)}}{r^{(j')}}\Bigr)\Bigr)^{-1}.$$
--   For $j = 1$ the first factor is $1$, because $r^{(0)} = 0$, so $\sigma^{(1)} = \bigl(1 + \sum_{j'=2}^m (1 - r^{(j'-1)}/r^{(j')})\bigr)^{-1}$.
--
--   This closed form is the existence-and-uniqueness half of Proposition 1 for $\sigma$, and it is the starting point of the comparison (12) between $\sigma^{(1)}$ and the price-continuum ratio $1/(1 + \ln(r^{(m)}/r^{(1)}))$.
--
--   **Formalization Note** The $j = 1$ case uses `price r 0 = 0`, the paper's convention $r^{(0)} := 0$.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, p. 38, App. A, proof of Proposition 1 (explicit value of σ⁽ʲ⁾)

import Mathlib
import Definitions.Def_MultiPriceOnline_Ratios_Setting

namespace MultiPriceOnline.Ratios

open Finset

theorem explicit_sigma (m : ℕ) (hm : 1 ≤ m) (r : ℕ → ℝ) (hr : MultiPriceOnline.Balance.IsPriceSet m r)
    (σ : ℕ → ℝ) (hσ : MultiPriceOnline.Balance.IsBQLimits m r σ) :
    ∀ j ∈ Icc 1 m,
      σ j = (1 - MultiPriceOnline.Hardness.price r (j - 1) / r j) /
        (1 + ∑ j' ∈ Icc 2 m, (1 - r (j' - 1) / r j')) := by sorry

end MultiPriceOnline.Ratios
