-- Prove2me | Theorems.Thm_LL_Decomp1528a_mertens1_abs
-- name    : LL_Decomp1528a.mertens1_abs
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-28T17:15:14.490954+00:00
-- url     : https://prove2.me/theorems/04497b59-197d-4e00-a778-375fe85ff1a9
-- title:
--   Mertens first theorem with explicit absolute error $2$
-- statement:
--   For every real number $x\ge1$, $\left|\sum_{p\le\lfloor x\rfloor}\frac{\log p}{p}-\log x\right|\le2$, where the sum runs over primes and $\log$ denotes the natural logarithm.
-- source:
--   Rosser and Schoenfeld 1962, equations 3.21 and 3.24, p. 70; lab unit U-1528 assembly mertens1_abs, in the explicit-estimate context of Campbell 2026, Section 4. Source context: https://arxiv.org/abs/2608.09488v1

import Mathlib

open Real Finset Chebyshev

namespace LL_Decomp1528a
theorem mertens1_abs {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p - log x| ≤ 2 := by sorry
end LL_Decomp1528a
