-- Prove2me | Theorems.Thm_LefebvreVariations_gilbreath_first_hundred_rows
-- name    : LefebvreVariations.gilbreath_first_hundred_rows
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:46:52.691114+00:00
-- url     : https://prove2.me/theorems/66dd3b2b-a4a8-4f04-a796-988a8efd5095
-- title:
--   Lefebvre's variations: Gilbreath's conjecture for the first hundred rows
-- statement:
--   This verifies Gilbreath's conjecture for the first hundred rows.
--
--   Let $d_0(i)=p_{i+1}$ be the sequence of primes $2,3,5,7,\dots$ and $d_{k+1}(i)=|d_k(i+1)-d_k(i)|$ the successive rows of absolute differences. Then
--
--   $$
--   d_k(0)=1\qquad\text{for }1\le k\le100 .
--   $$
--
--   Gilbreath's conjecture asserts $d_k(0)=1$ for every $k\ge1$; it has been checked numerically far beyond this range (Odlyzko) but is open. The first hundred rows involve only the first $101$ primes, up to $547$, and are certified here by exact computation, extending the platform's verification of the first four rows.
--
--   **Formalization Note** The triangle is the mission's `d k i` built from `Nat.nth Nat.Prime`; the proof identifies the first $101$ values of `Nat.nth Nat.Prime` with an explicit list.
-- source:
--   Conjecture: N. L. Gilbreath (1958), see R. B. Killgrove and K. E. Ralston, On a conjecture concerning the primes, Math. Tables Aids Comput. 13 (1959), 121–122 (verification of the first 63 419 rows); A. M. Odlyzko, Iterated absolute values of differences of consecutive primes, Math. Comp. 61 (1993), 373–380. Parent problem: Gilbreath.gilbreath_conjecture.

import Mathlib
import Definitions.Def_gilbreath_triangle

set_option autoImplicit false

namespace LefebvreVariations

/-- **Gilbreath's conjecture for the first 100 rows**: the leading entry of each of the first
hundred rows of the triangle of iterated absolute differences of the primes is `1`
(row `k` only involves the first `k + 1` primes, so this is a finite check on the primes up to
`547`). Gilbreath (1958), reported in Killgrove–Ralston, *On a conjecture concerning the primes*,
Math. Tables Aids Comput. 13 (1959) 121–122 (first 63419 primes); Odlyzko, *Iterated absolute
values of differences of consecutive primes*, Math. Comp. 61 (1993) 373–380. -/
theorem gilbreath_first_hundred_rows (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 100) :
    Gilbreath.d k 0 = 1 := by
  sorry

end LefebvreVariations
