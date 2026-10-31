-- Prove2me | Theorems.Thm_MinBuying_exchangeable_construction_revenue
-- name    : MinBuying.exchangeable_construction_revenue
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T17:37:02.619647+00:00
-- url     : https://prove2.me/theorems/3ae3b612-2926-4ab9-9c75-ff953cb1e0c8
-- title:
--   Revenue bounds for the explicit exchangeable-gap construction
-- statement:
--   For every positive item count $n$, the explicit exchangeableGapLaw has uniform-price revenue at most one for every nonnegative price and strictly positive uniform revenue at price two. Its expected revenue at the designated differentiated prices $r_i=4^i$ is at least $(3/8)\sum_{i=0}^{n-1}\binom{n-1-i}{k_i-1}/\binom{n}{k_i}$, where $k_i=\max\{1,\lfloor n/[2(i+1)]\rfloor\}$.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript. https://doi.org/10.2139/ssrn.5178133 . Proof of Theorem 3, ec5–ec7 (PDF pp.32–34): uniform-price upper bound (EC.8), differentiated-price subset count (EC.9), with reversed ascending type indices.

import Definitions.Def_MinBuying_ExchangeableConstruction

open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section

namespace MinBuying

theorem exchangeable_construction_revenue (n : ℕ) (hn : 0 < n) :
    (∀ q : ℝ, 0 ≤ q → uniformRevenue (exchangeableGapLaw n) q ≤ 1) ∧
    0 < uniformRevenue (exchangeableGapLaw n) 2 ∧
    (3/8:ℝ) * (∑ i : Fin n, ((n-1-i.val).choose (gapTypeSize n i-1) : ℝ) /
      (n.choose (gapTypeSize n i) : ℝ)) ≤ Revenue (exchangeableGapLaw n) (gapPrices n)  := by
  sorry

end MinBuying
