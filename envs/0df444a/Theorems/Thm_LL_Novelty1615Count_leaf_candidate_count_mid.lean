-- Prove2me | Theorems.Thm_LL_Novelty1615Count_leaf_candidate_count_mid
-- name    : LL_Novelty1615Count.leaf_candidate_count_mid
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-25T03:56:12.934984+00:00
-- url     : https://prove2.me/theorems/ae0bb707-3827-4704-9e96-5ea6f9cdaf4d
-- title:
--   At most $99$ divisors $p-1$ of $L$ in $[1965600,4600000)$ off the list
-- statement:
--   Let $L$ be a natural number with $1965600\le L<4600000$ that is not one of the $33$ values in midList, and let $T$ be a finite set of natural numbers such that every $d\in T$ divides $L$ and is of the form $d=p-1$ for some prime $p\ge 5$. Then $T$ has fewer than $100$ elements.
-- source:
--   Counting step for Erdős problem 273, https://www.erdosproblems.com/273, on covering systems with distinct moduli $p-1$; from the Lean Lab analysis bounding such systems with lcm below $8000000$.

import Mathlib
import Definitions.Def_LL_Novelty1615Count_midList

namespace LL_Novelty1615Count
theorem leaf_candidate_count_mid (L : ℕ) (hlo : 1965600 ≤ L) (hhi : L < 4600000)
    (hnot : L ∉ midList) (T : Finset ℕ)
    (hdvd : ∀ d ∈ T, d ∣ L) (hform : ∀ d ∈ T, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ d = p - 1) :
    T.card < 100 := by sorry
end LL_Novelty1615Count
