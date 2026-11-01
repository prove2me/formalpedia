-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_l2Generated_tracialExpectation
-- name    : OAI.KadisonSimilarity.TracialCornerGeometry.l2Generated_tracialExpectation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T08:50:08.350819+00:00
-- url     : https://prove2.me/theorems/5c00aa5f-311e-4115-85cd-d98ec8aad0f9
-- title:
--   OAI.KadisonSimilarity.TracialCornerGeometry.l2Generated_tracialExpectation: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.TracialCornerGeometry.l2Generated_tracialExpectation` of [lean/OAI/Analysis/KadisonSimilarity/Tracial/NormalTracialExpectations.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/NormalTracialExpectations.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity.TracialCornerGeometry`, with `open Generator.Tracial UltrapowerBridge`):
--
--   ```lean
--   theorem l2Generated_tracialExpectation
--       (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
--       (M : VonNeumannAlgebra H) (hrange : G.left.range = M.toStarSubalgebra)
--       (S : StarSubalgebra ℂ A) :
--       Nonempty (TracialExpectation G.trace (G.l2GeneratedAlgebra S))
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonSimilarity.TracialCornerGeometry` and `OAI.KadisonSimilarity.TracialExpectation` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra` (definitions bundle `OAIQ075A023` of this split).
--
--   **Used by.** The proof of `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_from_local_published_inputs` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/NormalTracialExpectations.lean (declaration OAI.KadisonSimilarity.TracialCornerGeometry.l2Generated_tracialExpectation)

import Mathlib
import Definitions.Def_OAIQ075A023

section

attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
namespace TracialCornerGeometry

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry A H)

theorem l2Generated_tracialExpectation
    (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (M : VonNeumannAlgebra H) (hrange : G.left.range = M.toStarSubalgebra)
    (S : StarSubalgebra ℂ A) :
    Nonempty (TracialExpectation G.trace (G.l2GeneratedAlgebra S)) := by
  sorry

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end
