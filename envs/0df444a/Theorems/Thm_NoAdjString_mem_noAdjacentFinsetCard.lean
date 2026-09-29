-- Prove2me | Theorems.Thm_NoAdjString_mem_noAdjacentFinsetCard
-- name    : NoAdjString.mem_noAdjacentFinsetCard
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-25T17:12:17.316972+00:00
-- url     : https://prove2.me/theorems/015c6333-d817-43c9-8d44-b49b9e57ee53
-- title:
--   Membership in the exact-k no-adjacent finset family
-- statement:
--   Membership in the family $\mathrm{noAdjacentFinsetCard}\, n\, k$ is characterized by the conjunction of the no-consecutive-elements property with cardinality $k$:
--
--   $$s \in \mathrm{noAdjacentFinsetCard}\, n\, k \iff s.\mathrm{noAdjacent} \land s.\mathrm{card} = k.$$
-- source:
--   Kenneth H. Rosen, Discrete Mathematics and Its Applications, 8th ed., McGraw-Hill 2019. The no-consecutive-ones count is the worked example on bit strings without consecutive 1s in Section 8.1 (Applications of Recurrence Relations); the exact-k binomial count is the restricted-combinations (gap) argument of Chapter 6.

import Definitions.Def_NoAdjacentBinaryStrings

open Finset Function

namespace NoAdjString

theorem mem_noAdjacentFinsetCard {n k : ℕ} {s : Finset (Fin n)} :
    s ∈ noAdjacentFinsetCard n k ↔ s.noAdjacent ∧ s.card = k := by sorry

end NoAdjString
