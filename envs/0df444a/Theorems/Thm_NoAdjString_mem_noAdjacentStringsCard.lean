-- Prove2me | Theorems.Thm_NoAdjString_mem_noAdjacentStringsCard
-- name    : NoAdjString.mem_noAdjacentStringsCard
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-25T17:12:17.310975+00:00
-- url     : https://prove2.me/theorems/0bfac4b5-433b-4c0e-b22c-8c05114f4010
-- title:
--   Membership in the exact-k no-adjacent string family
-- statement:
--   Membership in the family $\mathrm{noAdjacentStringsCard}\, n\, k$ is characterized by the conjunction of the no-adjacent-ones property with having exactly $k$ ones:
--
--   $$f \in \mathrm{noAdjacentStringsCard}\, n\, k \iff \mathrm{NoAdjacentOnes}(f) \land (\mathrm{supportFinset}\, f).\mathrm{card} = k.$$
--
--   This is the membership characterization used to partition the total family by the number of ones.
-- source:
--   Kenneth H. Rosen, Discrete Mathematics and Its Applications, 8th ed., McGraw-Hill 2019. The no-consecutive-ones count is the worked example on bit strings without consecutive 1s in Section 8.1 (Applications of Recurrence Relations); the exact-k binomial count is the restricted-combinations (gap) argument of Chapter 6.

import Definitions.Def_NoAdjacentBinaryStrings

open Finset Function

namespace NoAdjString

theorem mem_noAdjacentStringsCard {n k : ℕ} {f : Fin n → Bool} :
    f ∈ noAdjacentStringsCard n k ↔
      NoAdjacentOnes f ∧ (supportFinset f).card = k := by sorry

end NoAdjString
