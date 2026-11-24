-- Prove2me | Theorems.Thm_LL_Erdos273Count_leaf_candidate_count_small
-- name    : LL_Erdos273Count.leaf_candidate_count_small
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-22T11:32:22.083965+00:00
-- url     : https://prove2.me/theorems/7cce2ed3-5754-4df9-9f87-26d9f6bbe08c
-- title:
--   At most $99$ divisors of the form $p-1$, $p\ge5$ prime, below $1965600$
-- statement:
--   Let $L$ be a natural number with $0<L<1965600$, and let $T$ be a finite set of natural numbers such that every $d\in T$ divides $L$ and is of the form $d=p-1$ for some prime $p\ge 5$. Then $T$ has fewer than $100$ elements, that is, $L$ has at most $99$ divisors $d$ with $d+1$ a prime at least $5$.
-- source:
--   Counting step for Erdős problem 273, https://www.erdosproblems.com/273, on covering systems with distinct moduli $p-1$; from the Lean Lab analysis bounding such systems with lcm below $8000000$.

import Mathlib

namespace LL_Erdos273Count
theorem leaf_candidate_count_small (L : ℕ) (hL0 : 0 < L) (hL : L < 1965600) (T : Finset ℕ)
    (hdvd : ∀ d ∈ T, d ∣ L) (hform : ∀ d ∈ T, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ d = p - 1) :
    T.card < 100 := by sorry
end LL_Erdos273Count
