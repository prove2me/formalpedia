-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_arcWidth_pos
-- name    : OAI.KadisonSimilarity.arcWidth_pos
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-03T16:41:48.035831+00:00
-- url     : https://prove2.me/theorems/7f3c28a8-9bfa-4597-9c36-abb4f3bb1187
-- title:
--   OAI.KadisonSimilarity.arcWidth_pos: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.arcWidth_pos` of [lean/OAI/Analysis/KadisonSimilarity/FreeProduct/HankelBounds.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/HankelBounds.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity`, with `open Finset`):
--
--   ```lean
--   theorem arcWidth_pos {N : ℕ} (hN : 0 < N) : 0 < arcWidth N
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonSimilarity.arcWidth` (definitions bundle `OAIQ075A006` of this split).
--
--   **Used by.** The proofs of `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_of_published_local_models` and `OAI.KadisonSimilarity.free_corner_from_multiplicity_propagation` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/HankelBounds.lean (declaration OAI.KadisonSimilarity.arcWidth_pos)

import Mathlib
import Definitions.Def_OAIQ075A006

section

attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KadisonSimilarity

open Finset

theorem arcWidth_pos {N : ℕ} (hN : 0 < N) : 0 < arcWidth N := by
  sorry

end KadisonSimilarity

end

end OAI
end
