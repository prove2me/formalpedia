-- Prove2me | Theorems.Thm_LL_Novelty1615Count_leaf_candidate_count_top
-- name    : LL_Novelty1615Count.leaf_candidate_count_top
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-25T03:56:42.19979+00:00
-- url     : https://prove2.me/theorems/f7c594f4-5176-4ab4-86b6-c0957e74eb34
-- title:
--   At most $99$ divisors $p-1$ of $L$ in $[4600000,8000000)$ off the list
-- statement:
--   Let $L$ be a natural number with $4600000\le L<8000000$ that is neither one of the $91$ values in topList nor one of $5012280, 7022400, 7425600, 7876440$, and let $T$ be a finite set of natural numbers such that every $d\in T$ divides $L$ and is of the form $d=p-1$ for some prime $p\ge 5$. Then $T$ has fewer than $100$ elements.
-- source:
--   Counting step for Erdős problem 273, https://www.erdosproblems.com/273, on covering systems with distinct moduli $p-1$; from the Lean Lab analysis bounding such systems with lcm below $8000000$.

import Mathlib
import Definitions.Def_LL_Novelty1615Count_topList

namespace LL_Novelty1615Count
theorem leaf_candidate_count_top (L : ℕ) (hlo : 4600000 ≤ L) (hhi : L < 8000000)
    (hnot : L ∉ topList) (hout : L ∉ ({5012280, 7022400, 7425600, 7876440} : Finset ℕ))
    (T : Finset ℕ)
    (hdvd : ∀ d ∈ T, d ∣ L) (hform : ∀ d ∈ T, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ d = p - 1) :
    T.card < 100 := by sorry
end LL_Novelty1615Count
