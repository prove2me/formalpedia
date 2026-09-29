-- Prove2me | Theorems.Thm_NoAdjString_noAdjacentOnes_iff_noAdjacent
-- name    : NoAdjString.noAdjacentOnes_iff_noAdjacent
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-25T17:12:19.412474+00:00
-- url     : https://prove2.me/theorems/70c28bd2-6760-4219-b47e-8f72ab1b4681
-- title:
--   No-adjacent-ones property: strings vs support finsets
-- statement:
--   The predicate on a binary string $f : \mathrm{Fin}\, n \to \mathrm{Bool}$ saying that no two consecutive entries are true is equivalent to the predicate on its support finset saying that no two consecutive positions belong to it:
--
--   $$\mathrm{NoAdjacentOnes}(f) \iff (\mathrm{supportFinset}\, f).\mathrm{noAdjacent}.$$
--
--   This lemma connects the binary-string and finset formulations of the family, so that the counting arguments can be carried out with finsets and then transferred back to strings.
-- source:
--   Kenneth H. Rosen, Discrete Mathematics and Its Applications, 8th ed., McGraw-Hill 2019. The no-consecutive-ones count is the worked example on bit strings without consecutive 1s in Section 8.1 (Applications of Recurrence Relations); the exact-k binomial count is the restricted-combinations (gap) argument of Chapter 6.

import Definitions.Def_NoAdjacentBinaryStrings

open Finset Function

namespace NoAdjString

theorem noAdjacentOnes_iff_noAdjacent {n : ℕ} (f : Fin n → Bool) :
    NoAdjacentOnes f ↔ (supportFinset f).noAdjacent := by sorry

end NoAdjString
