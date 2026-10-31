-- Prove2me | Theorems.Thm_LL_Decomp1528b_mertens_prod_lower
-- name    : LL_Decomp1528b.mertens_prod_lower
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-30T14:09:10.463692+00:00
-- url     : https://prove2.me/theorems/151155c7-01db-4c0b-9cf3-efa83b4f8fa2
-- title:
--   Elementary lower bound for the Mertens product
-- statement:
--   For every real $x\ge 2$, $\dfrac{1}{1500\log x}\le\prod_{p\le\lfloor x\rfloor}\left(1-\dfrac1p\right)$, the product being over primes $p\le\lfloor x\rfloor$, with the real number $p$ obtained by casting the natural number $p$.
-- source:
--   Campbell, arXiv 2608.09488 v1, Section 4; compare Rosser and Schoenfeld, Illinois J. Math. 6 (1962), p. 70, eq. 3.25

import Mathlib

open Real Finset Filter Topology

namespace LL_Decomp1528b
theorem mertens_prod_lower {x : ℝ} (hx : 2 ≤ x) :
    1 / (1500 * log x) ≤ ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (1 : ℝ) / p) := by sorry
end LL_Decomp1528b
