-- Prove2me | Theorems.Thm_MinBuying_exchangeable_subset_bound
-- name    : MinBuying.exchangeable_subset_bound
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T17:35:41.201545+00:00
-- url     : https://prove2.me/theorems/6d685493-9abe-44ca-89f0-db520661bcac
-- title:
--   Subset probability bound for the exchangeable construction
-- statement:
--   For positive integer $n$ and integer $0\le i<n$, let $k=\max\{1,\lfloor n/[2(n-i)]\rfloor\}$. Then $\binom{i}{k-1}/\binom{n}{k}\ge 1/[4(n-i)]$. The left side is the probability that a uniformly chosen $k$-element subset of $\{0,\ldots,n-1\}$ has maximum element $i$.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript. https://doi.org/10.2139/ssrn.5178133 . Proof of Theorem 3, ec6–ec7, Eq.(EC.9) and the following lower bound, translated to zero-based indices.

import Mathlib

namespace MinBuying

theorem exchangeable_subset_bound (n i : ℕ) (hn : 0 < n) (hi : i < n) :
    let k := max 1 (n / (2*(n-i)))
    1 / (4*((n-i : ℕ) : ℝ)) ≤ (i.choose (k-1) : ℝ) / (n.choose k : ℝ) := by
  sorry

end MinBuying
