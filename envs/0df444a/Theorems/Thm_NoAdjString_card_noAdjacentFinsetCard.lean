-- Prove2me | Theorems.Thm_NoAdjString_card_noAdjacentFinsetCard
-- name    : NoAdjString.card_noAdjacentFinsetCard
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-25T17:12:33.278446+00:00
-- url     : https://prove2.me/theorems/f2207bd6-f966-4ec7-917c-72bc0ba923e9
-- title:
--   Count of k-element finsets with no consecutive elements
-- statement:
--   The number of $k$-element finsets of $\mathrm{Fin}\, n$ containing no two consecutive elements is
--
--   $$\#(\mathrm{noAdjacentFinsetCard}\, n\, k) = \binom{n+1-k}{k}.$$
--
--   The bijection $\mathrm{noAdjacentFinsetCardEquiv}$ identifies such finsets with $\mathrm{GapMono}\, n\, k$, whose cardinality is the binomial coefficient.
-- source:
--   Kenneth H. Rosen, Discrete Mathematics and Its Applications, 8th ed., McGraw-Hill 2019. The no-consecutive-ones count is the worked example on bit strings without consecutive 1s in Section 8.1 (Applications of Recurrence Relations); the exact-k binomial count is the restricted-combinations (gap) argument of Chapter 6.

import Definitions.Def_NoAdjacentGapEquiv

open Finset Function

namespace NoAdjString

theorem card_noAdjacentFinsetCard (n k : ℕ) :
    (noAdjacentFinsetCard n k).card = Nat.choose (n + 1 - k) k := by sorry

end NoAdjString
