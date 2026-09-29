-- Prove2me | Theorems.Thm_NoAdjString_noAdjacentStringsCard_image
-- name    : NoAdjString.noAdjacentStringsCard_image
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-25T17:12:20.847985+00:00
-- url     : https://prove2.me/theorems/3aa371ee-ba68-48fe-80ab-40b17bea23e4
-- title:
--   Exact-k no-adjacent strings vs exact-k no-adjacent finsets
-- statement:
--   Under $\mathrm{boolFinsetEquiv}$, the family of length-$n$ no-adjacent strings with exactly $k$ ones maps exactly onto the family of $k$-element finsets with no consecutive elements:
--
--   $$\mathrm{image}(\mathrm{noAdjacentStringsCard}\, n\, k) = \mathrm{noAdjacentFinsetCard}\, n\, k.$$
-- source:
--   Kenneth H. Rosen, Discrete Mathematics and Its Applications, 8th ed., McGraw-Hill 2019. The no-consecutive-ones count is the worked example on bit strings without consecutive 1s in Section 8.1 (Applications of Recurrence Relations); the exact-k binomial count is the restricted-combinations (gap) argument of Chapter 6.

import Definitions.Def_NoAdjacentBinaryStrings

open Finset Function

namespace NoAdjString

theorem noAdjacentStringsCard_image (n k : ℕ) :
    (noAdjacentStringsCard n k).image (boolFinsetEquiv n) = noAdjacentFinsetCard n k := by sorry

end NoAdjString
