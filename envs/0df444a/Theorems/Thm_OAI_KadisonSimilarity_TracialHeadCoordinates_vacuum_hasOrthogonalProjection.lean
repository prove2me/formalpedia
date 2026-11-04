-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_TracialHeadCoordinates_vacuum_hasOrthogonalProjection
-- name    : OAI.KadisonSimilarity.TracialHeadCoordinates.vacuum_hasOrthogonalProjection
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-03T17:19:37.486212+00:00
-- url     : https://prove2.me/theorems/e8acb84e-6a63-41fa-8866-251babb3ade1
-- title:
--   OAI.KadisonSimilarity.TracialHeadCoordinates.vacuum_hasOrthogonalProjection: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.TracialHeadCoordinates.vacuum_hasOrthogonalProjection` of [lean/OAI/Analysis/KadisonSimilarity/Tracial/TracialHeadCoordinates.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/TracialHeadCoordinates.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity.TracialHeadCoordinates`):
--
--   ```lean
--   theorem vacuum_hasOrthogonalProjection (hτ : GD.trace 1 = 1) :
--       W.vacuum.HasOrthogonalProjection
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonSimilarity.TracialCornerGeometry` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.TracialHeadCoordinates` and `OAI.KadisonSimilarity.TracialHeadCoordinates.vacuum` (definitions bundle `OAIQ075A024` of this split).
--
--   **Used by.** The proof of `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_estimate_of_published_words` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/TracialHeadCoordinates.lean (declaration OAI.KadisonSimilarity.TracialHeadCoordinates.vacuum_hasOrthogonalProjection)

import Mathlib
import Definitions.Def_OAIQ075A024

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity

variable {D P E H F : Type*} [CStarAlgebra D] [CStarAlgebra P]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

namespace TracialHeadCoordinates

variable {GD : TracialCornerGeometry D E} {G : TracialCornerGeometry P H}
  {ι : D →⋆ₐ[ℂ] P} (W : TracialHeadCoordinates GD G ι F)

theorem vacuum_hasOrthogonalProjection (hτ : GD.trace 1 = 1) :
    W.vacuum.HasOrthogonalProjection := by
  sorry

end TracialHeadCoordinates
end KadisonSimilarity

end

end OAI
end
