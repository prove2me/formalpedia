-- Prove2me | Theorems.Thm_NoAdjString_card_gapMono
-- name    : NoAdjString.card_gapMono
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-25T17:12:37.758986+00:00
-- url     : https://prove2.me/theorems/0a62a884-5fec-482f-bd04-adc4d47b763b
-- title:
--   Count of gap-2 monotone position tuples
-- statement:
--   The carrier $\mathrm{GapMono}\, n\, k$ of strictly monotone position embeddings whose successive values differ by at least two has cardinality
--
--   $$\#(\mathrm{GapMono}\, n\, k) = \binom{n+1-k}{k}.$$
--
--   Gap compression, which subtracts each selected position's index, gives a bijection with strictly monotone $k$-tuples in $\mathrm{Fin}(n+1-k)$, and such tuples are in bijection with the $k$-element finsets, counted by the binomial coefficient. This is the central enumerative lemma for strings with exactly $k$ non-adjacent ones.
-- source:
--   Kenneth H. Rosen, Discrete Mathematics and Its Applications, 8th ed., McGraw-Hill 2019. The no-consecutive-ones count is the worked example on bit strings without consecutive 1s in Section 8.1 (Applications of Recurrence Relations); the exact-k binomial count is the restricted-combinations (gap) argument of Chapter 6.

import Definitions.Def_NoAdjacentGapEquiv

open Finset Function

namespace NoAdjString

theorem card_gapMono (n k : ℕ) :
    Fintype.card (GapMono n k) = Nat.choose (n + 1 - k) k := by sorry

end NoAdjString
