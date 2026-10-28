-- Prove2me | Theorems.Thm_LL_Decomp1528a_sum_log_div_pp1_split
-- name    : LL_Decomp1528a.sum_log_div_pp1_split
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-28T17:13:33.177329+00:00
-- url     : https://prove2.me/theorems/85daf4e1-ff6c-4ecd-9f0e-9b652052e3ef
-- title:
--   Prime sum bounded by a fixed head and an integer tail
-- statement:
--   For every natural number $n$, $\sum_{p\le n}\frac{\log p}{p(p-1)}\le\sum_{p\le1000}\frac{\log p}{p(p-1)}+\sum_{1000<m\le n}\frac{\log m}{m(m-1)}$, where $p$ runs over primes and $m$ over integers.
-- source:
--   Elementary finite-sum comparison in lab unit U-1528. Source context: https://arxiv.org/abs/2608.09488v1

import Mathlib

open Real Finset Chebyshev

namespace LL_Decomp1528a
theorem sum_log_div_pp1_split (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤
      ∑ p ∈ Nat.primesLE 1000, log p / ((p : ℝ) * ((p : ℝ) - 1)) +
        ∑ m ∈ Ioc 1000 n, log m / ((m : ℝ) * ((m : ℝ) - 1)) := by sorry
end LL_Decomp1528a
