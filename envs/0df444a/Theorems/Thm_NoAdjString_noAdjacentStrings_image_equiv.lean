-- Prove2me | Theorems.Thm_NoAdjString_noAdjacentStrings_image_equiv
-- name    : NoAdjString.noAdjacentStrings_image_equiv
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-25T17:12:23.516216+00:00
-- url     : https://prove2.me/theorems/bcea25ec-fe38-403f-8af3-7608fdcfb588
-- title:
--   No-adjacent strings vs no-adjacent finsets under the canonical equivalence
-- statement:
--   Under the canonical equivalence $\mathrm{boolFinsetEquiv}$ between binary strings and finsets, the family of length-$n$ strings with no adjacent ones maps exactly onto the family of finsets of $\mathrm{Fin}\, n$ with no consecutive elements:
--
--   $$\mathrm{image}(\mathrm{noAdjacentStrings}\, n) = \mathrm{noAdjacentFinset}\, n.$$
-- source:
--   Kenneth H. Rosen, Discrete Mathematics and Its Applications, 8th ed., McGraw-Hill 2019. The no-consecutive-ones count is the worked example on bit strings without consecutive 1s in Section 8.1 (Applications of Recurrence Relations); the exact-k binomial count is the restricted-combinations (gap) argument of Chapter 6.

import Definitions.Def_NoAdjacentBinaryStrings

open Finset Function

namespace NoAdjString

theorem noAdjacentStrings_image_equiv (n : ℕ) :
    (noAdjacentStrings n).image (boolFinsetEquiv n) = noAdjacentFinset n := by sorry

end NoAdjString
