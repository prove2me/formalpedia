-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_dicksonTwoBound_proved
-- name    : OAI.KadisonSimilarity.dicksonTwoBound_proved
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T08:27:50.300111+00:00
-- url     : https://prove2.me/theorems/832d08fe-d11a-4388-9f0a-4b87287fc14d
-- title:
--   OAI.KadisonSimilarity.dicksonTwoBound_proved: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.dicksonTwoBound_proved` of [lean/OAI/Analysis/KadisonSimilarity/Derivation/DicksonDischarge.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Derivation/DicksonDischarge.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity`):
--
--   ```lean
--   theorem dicksonTwoBound_proved : DicksonTwoBound (A := A) H
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonSimilarity.DicksonTwoBound` (definitions bundle `OAIQ075A010` of this split).
--
--   **Used by.** The proofs of `OAI.KadisonSimilarity.TracialRepeatedWordRealization.propagation_on_base_of_published_inputs`, `OAI_KadisonSimilarity_exists_corner_intertwiner_of_column_tests`, `OAI.KadisonSimilarity.uniformCommutatorEstimate`, `OAI_KadisonSimilarity_uniformCommutatorEstimate_of_published`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Derivation/DicksonDischarge.lean (declaration OAI.KadisonSimilarity.dicksonTwoBound_proved)

import Mathlib
import Definitions.Def_OAIQ075A010

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem dicksonTwoBound_proved : DicksonTwoBound (A := A) H := by
  sorry

end KadisonSimilarity

end

end OAI
end
