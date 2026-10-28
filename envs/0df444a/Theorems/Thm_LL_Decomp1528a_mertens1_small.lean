-- Prove2me | Theorems.Thm_LL_Decomp1528a_mertens1_small
-- name    : LL_Decomp1528a.mertens1_small
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-28T17:13:46.806796+00:00
-- url     : https://prove2.me/theorems/00d3a520-4a3e-4a79-bf39-ac7eafa102fe
-- title:
--   Explicit Mertens bound on $1\le x<5$
-- statement:
--   For every real number $x$ with $1\le x<5$, $\left|\sum_{p\le\lfloor x\rfloor}\frac{\log p}{p}-\log x\right|\le2$, where the sum runs over primes.
-- source:
--   Lab unit U-1528, small-range component of the explicit Mertens estimate; compare Rosser and Schoenfeld 1962, equations 3.21 and 3.24. Source context: https://arxiv.org/abs/2608.09488v1

import Mathlib

open Real Finset Chebyshev

namespace LL_Decomp1528a
theorem mertens1_small {x : ℝ} (hx : 1 ≤ x) (hx5 : x < 5) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p - log x| ≤ 2 := by sorry
end LL_Decomp1528a
