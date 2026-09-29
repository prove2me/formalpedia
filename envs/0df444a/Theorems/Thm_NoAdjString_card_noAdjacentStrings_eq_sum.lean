-- Prove2me | Theorems.Thm_NoAdjString_card_noAdjacentStrings_eq_sum
-- name    : NoAdjString.card_noAdjacentStrings_eq_sum
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-25T17:12:24.383184+00:00
-- url     : https://prove2.me/theorems/a85dec08-c6e0-47df-b1e7-fc3152815d00
-- title:
--   Total no-adjacent string count as a sum over k
-- statement:
--   The total number of length-$n$ strings with no adjacent ones equals the sum, over the number $k$ of ones, of the exact-$k$ counts:
--
--   $$\#(\mathrm{noAdjacentStrings}\, n) = \sum_{k=0}^{n} \binom{n+1-k}{k}.$$
--
--   The families for distinct $k$ are pairwise disjoint because their members have distinct support cardinalities.
-- source:
--   Kenneth H. Rosen, Discrete Mathematics and Its Applications, 8th ed., McGraw-Hill 2019. The no-consecutive-ones count is the worked example on bit strings without consecutive 1s in Section 8.1 (Applications of Recurrence Relations); the exact-k binomial count is the restricted-combinations (gap) argument of Chapter 6.

import Definitions.Def_NoAdjacentBinaryStrings

open Finset Function

namespace NoAdjString

theorem card_noAdjacentStrings_eq_sum (n : ℕ) :
    (noAdjacentStrings n).card =
      ∑ k ∈ Finset.range (n + 1), Nat.choose (n + 1 - k) k := by sorry

end NoAdjString
