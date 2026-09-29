-- Prove2me | Theorems.Thm_NoAdjString_card_noAdjacentStringsCard
-- name    : NoAdjString.card_noAdjacentStringsCard
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-25T17:12:25.476995+00:00
-- url     : https://prove2.me/theorems/a2b909e9-a25e-4af5-b655-9c77899981ad
-- title:
--   Count of length-n strings with k non-adjacent ones
-- statement:
--   The number of length-$n$ binary strings with no adjacent ones and exactly $k$ ones is
--
--   $$\#(\mathrm{noAdjacentStringsCard}\, n\, k) = \binom{n+1-k}{k}.$$
--
--   Placing $k$ non-adjacent marks among $n$ positions forces a gap after each mark except the last; the gap bijection identifies these placements with the choice of $k$ positions among the $n+1-k$ available slots.
-- source:
--   Kenneth H. Rosen, Discrete Mathematics and Its Applications, 8th ed., McGraw-Hill 2019. The no-consecutive-ones count is the worked example on bit strings without consecutive 1s in Section 8.1 (Applications of Recurrence Relations); the exact-k binomial count is the restricted-combinations (gap) argument of Chapter 6.

import Definitions.Def_NoAdjacentBinaryStrings

open Finset Function

namespace NoAdjString

theorem card_noAdjacentStringsCard (n k : ℕ) :
    (noAdjacentStringsCard n k).card = Nat.choose (n + 1 - k) k := by sorry

end NoAdjString
