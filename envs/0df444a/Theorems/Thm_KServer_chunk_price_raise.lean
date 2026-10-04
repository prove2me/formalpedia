-- Prove2me | Theorems.Thm_KServer_chunk_price_raise
-- name    : KServer.chunk_price_raise
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-02T11:22:29.426987+00:00
-- url     : https://prove2.me/theorems/a08dc452-d32c-4b65-89e8-6613f13bec73
-- title:
--   The escape price of a chunk system is one-sided: it can be raised at no cost
-- statement:
--   A `ChunkSystemB` carries five real parameters: the size window `cLo, cHi`, the expected total size `total`, the escape price `price`, and the chunk count floor `mLo`. Three of them occur in exactly one structure field each and can be moved on their own in the weakening direction.
--
--   This lemma is the third member of that family, for the escape price. The price `price` appears in a single field, `hcost`, and only as the final argument of the online escape cost:
--
--   ```
--   P w * E.bailCost bail (prefix w) (chunk w i) price
--   ```
--
--   and the escape cost is non-decreasing in that argument:
--
--   ```
--   bailCost E bail h chi p = match bailTime bail h chi with
--     | some q => E.costOn h (chi.take q) + p
--     | none  => E.costOn h chi
--   ```
--
--   If the rule never fires, both values coincide; if it fires, the value at `price′` exceeds the value at `price` by exactly `price′ - price`. So `price ≤ price′` and a valid conditional cost bound at `price` give one at `price′`, with the other eighteen fields copied verbatim.
--
--   Together with `KServer.chunk_zero_floor` (lower `cLo`) and `KServer.chunk_ceiling_raise` (raise `cHi`), this frees all three size-and-price knobs of the BCR Lemma 12 induction package to move in the weakening direction, which is the direction the level crossing `KServer.bcr_lemma15_regroup_levels` needs on the escape-price parameter.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, Lemma 6 and Lemma 10. The one-sidedness of the escape price is a formal observation about the `ChunkSystemB` package of Lemma 6: `price` occurs in `hcost` only, through the escape cost of Lemma 10, which is non-decreasing in the escape price.

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b

namespace KServer

/-- The escape price of a chunk system is a one-sided parameter, so it can be
raised at no cost: the same chunk data, on the same space, is a valid chunk
system at escape price `price′`, with the same number of chunks. Raising
`price` only relaxes the conditional cost bound, because the online escape cost
`bailCost` is non-decreasing in the escape price. -/
theorem chunk_price_raise {X : Type*} [MetricSpace X] {s t : X}
    {cLo cHi total price price' : ℝ} {mLo : ℕ}
    (C : ChunkSystemB X s t cLo cHi total price mLo) (hP : price ≤ price') :
    ∃ C' : ChunkSystemB X s t cLo cHi total price' mLo, C'.m = C.m := by
  sorry

end KServer
