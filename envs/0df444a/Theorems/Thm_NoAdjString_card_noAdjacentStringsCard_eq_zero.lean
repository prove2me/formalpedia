-- Prove2me | Theorems.Thm_NoAdjString_card_noAdjacentStringsCard_eq_zero
-- name    : NoAdjString.card_noAdjacentStringsCard_eq_zero
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-25T17:12:31.855987+00:00
-- url     : https://prove2.me/theorems/1ebdcc05-de9b-4927-80f7-f69b0f122b4f
-- title:
--   Vanishing of the exact-k count when 2k > n+1
-- statement:
--   No length-$n$ string with no adjacent ones can contain $k$ ones when $2k > n+1$:
--
--   $$n+1 < 2k \implies \#(\mathrm{noAdjacentStringsCard}\, n\, k) = 0.$$
--
--   Indeed $k$ non-adjacent ones occupy at least $2k-1$ positions, so the binomial coefficient $\binom{n+1-k}{k}$ vanishes under this hypothesis.
-- source:
--   Kenneth H. Rosen, Discrete Mathematics and Its Applications, 8th ed., McGraw-Hill 2019. The no-consecutive-ones count is the worked example on bit strings without consecutive 1s in Section 8.1 (Applications of Recurrence Relations); the exact-k binomial count is the restricted-combinations (gap) argument of Chapter 6.

import Definitions.Def_NoAdjacentBinaryStrings

open Finset Function

namespace NoAdjString

theorem card_noAdjacentStringsCard_eq_zero (n k : ℕ) (h : n + 1 < 2 * k) :
    (noAdjacentStringsCard n k).card = 0 := by sorry

end NoAdjString
