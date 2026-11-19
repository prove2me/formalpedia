-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg536
-- name    : OAI.UniversalTensorSquare.sg536
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T22:40:56.089563+00:00
-- url     : https://prove2.me/theorems/4a1830b8-3197-4254-8be5-42d270fbb0f9
-- title:
--   OAI.UniversalTensorSquare.sg536: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg536` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg536 : RowSquare [4,2,1,1,1] [2,2,2,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_110All`, `OAI.UniversalTensorSquare.degreeTree39_13All`, `OAI.UniversalTensorSquare.degreeTree39_24All`, `OAI.UniversalTensorSquare.degreeTree39_60All`, `OAI.UniversalTensorSquare.degreeTree39_77All`, `OAI.UniversalTensorSquare.degreeTree43_102All`, `OAI.UniversalTensorSquare.degreeTree43_103All`, `OAI.UniversalTensorSquare.degreeTree43_236All`, `OAI.UniversalTensorSquare.degreeTree43_248All`, `OAI.UniversalTensorSquare.degreeTree43_253All`, `OAI.UniversalTensorSquare.degreeTree43_264All`, `OAI.UniversalTensorSquare.degreeTree43_394All`, `OAI.UniversalTensorSquare.degreeTree43_411All`, `OAI.UniversalTensorSquare.degreeTree43_508All`, `OAI.UniversalTensorSquare.degreeTree43_555All`, `OAI.UniversalTensorSquare.degreeTree43_580All`, `OAI.UniversalTensorSquare.degreeTree43_601All`, `OAI.UniversalTensorSquare.degreeTree43_616All`, `OAI.UniversalTensorSquare.degreeTree43_618All`, `OAI.UniversalTensorSquare.degreeTree43_97All`, `OAI.UniversalTensorSquare.degreeTree62_690All`, `OAI.UniversalTensorSquare.sg19089`, `OAI.UniversalTensorSquare.sg21884`, `OAI.UniversalTensorSquare.sg21992`, `OAI.UniversalTensorSquare.sg22049`, `OAI.UniversalTensorSquare.sg22063`, `OAI.UniversalTensorSquare.sg22279`, `OAI.UniversalTensorSquare.sg22355`, `OAI.UniversalTensorSquare.sg22370`, `OAI.UniversalTensorSquare.sg22535`, `OAI.UniversalTensorSquare.sg22687`, `OAI.UniversalTensorSquare.sg22782`, `OAI.UniversalTensorSquare.sg22810`, `OAI.UniversalTensorSquare.sg22962`, `OAI.UniversalTensorSquare.sg23046`, `OAI.UniversalTensorSquare.sg23070`, `OAI.UniversalTensorSquare.sg23215`, `OAI.UniversalTensorSquare.sg23219`, `OAI.UniversalTensorSquare.sg23651`, `OAI.UniversalTensorSquare.sg24833`, `OAI.UniversalTensorSquare.sg24875`, `OAI.UniversalTensorSquare.sg25162`, `OAI.UniversalTensorSquare.sg25214`, `OAI.UniversalTensorSquare.sg25215`, `OAI.UniversalTensorSquare.sg26141`, `OAI.UniversalTensorSquare.sg26153`, `OAI.UniversalTensorSquare.sg26577`, `OAI.UniversalTensorSquare.sg26606`, `OAI.UniversalTensorSquare.sg27233`, `OAI.UniversalTensorSquare.sg27372`, `OAI.UniversalTensorSquare.sg27422`, `OAI.UniversalTensorSquare.sg27453`, `OAI.UniversalTensorSquare.sg29367`, `OAI.UniversalTensorSquare.sg29598`, `OAI.UniversalTensorSquare.sg30888`, `OAI.UniversalTensorSquare.sg31298`, `OAI.UniversalTensorSquare.sg31408`, `OAI.UniversalTensorSquare.sg34641`, `OAI.UniversalTensorSquare.sg34749`, `OAI.UniversalTensorSquare.sg34751`, `OAI.UniversalTensorSquare.sg34771`, `OAI.UniversalTensorSquare.sg34905`, `OAI.UniversalTensorSquare.sg36004`, `OAI.UniversalTensorSquare.sg36673`, `OAI.UniversalTensorSquare.sg36754`, `OAI.UniversalTensorSquare.sg38043`, `OAI.UniversalTensorSquare.sg38454`, `OAI.UniversalTensorSquare.sg39603`, `OAI.UniversalTensorSquare.sg39606`, `OAI.UniversalTensorSquare.sg41239`, `OAI.UniversalTensorSquare.sg41890`, `OAI.UniversalTensorSquare.sg9220`, `OAI.UniversalTensorSquare.sg9222`, `OAI.UniversalTensorSquare.sg9223`, `OAI.UniversalTensorSquare.sg9250` and `OAI.UniversalTensorSquare.sg9286` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean (declaration OAI.UniversalTensorSquare.sg536)

import Mathlib
import Definitions.Def_OAIQ259US007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg536 : RowSquare [4,2,1,1,1] [2,2,2,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
