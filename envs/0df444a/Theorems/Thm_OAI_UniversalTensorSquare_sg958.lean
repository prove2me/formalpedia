-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg958
-- name    : OAI.UniversalTensorSquare.sg958
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-18T00:05:04.01554+00:00
-- url     : https://prove2.me/theorems/b5c8c2ff-24c9-434a-a111-0b3f19499e33
-- title:
--   OAI.UniversalTensorSquare.sg958: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg958` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg958 : RowSquare [5,3,1,1] [2,2,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_343All`, `OAI.UniversalTensorSquare.degreeTree43_583All`, `OAI.UniversalTensorSquare.degreeTree43_638All`, `OAI.UniversalTensorSquare.degreeTree62_522All`, `OAI.UniversalTensorSquare.degreeTree62_624All`, `OAI.UniversalTensorSquare.degreeTree62_723All`, `OAI.UniversalTensorSquare.sg12023`, `OAI.UniversalTensorSquare.sg12045`, `OAI.UniversalTensorSquare.sg21960`, `OAI.UniversalTensorSquare.sg22328`, `OAI.UniversalTensorSquare.sg23524`, `OAI.UniversalTensorSquare.sg24765`, `OAI.UniversalTensorSquare.sg26314`, `OAI.UniversalTensorSquare.sg26963`, `OAI.UniversalTensorSquare.sg26984`, `OAI.UniversalTensorSquare.sg27071`, `OAI.UniversalTensorSquare.sg27153`, `OAI.UniversalTensorSquare.sg28461`, `OAI.UniversalTensorSquare.sg28467`, `OAI.UniversalTensorSquare.sg28760`, `OAI.UniversalTensorSquare.sg29384`, `OAI.UniversalTensorSquare.sg29549`, `OAI.UniversalTensorSquare.sg30063`, `OAI.UniversalTensorSquare.sg30143`, `OAI.UniversalTensorSquare.sg30772`, `OAI.UniversalTensorSquare.sg31137`, `OAI.UniversalTensorSquare.sg31519`, `OAI.UniversalTensorSquare.sg31675`, `OAI.UniversalTensorSquare.sg31700`, `OAI.UniversalTensorSquare.sg31732`, `OAI.UniversalTensorSquare.sg31749`, `OAI.UniversalTensorSquare.sg37775`, `OAI.UniversalTensorSquare.sg37781`, `OAI.UniversalTensorSquare.sg38927`, `OAI.UniversalTensorSquare.sg38933`, `OAI.UniversalTensorSquare.sg40791`, `OAI.UniversalTensorSquare.sg40794`, `OAI.UniversalTensorSquare.sg40795`, `OAI.UniversalTensorSquare.sg6771`, `OAI.UniversalTensorSquare.sg6773`, `OAI.UniversalTensorSquare.sg6775`, `OAI.UniversalTensorSquare.sg6777` and `OAI.UniversalTensorSquare.sg6790` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean (declaration OAI.UniversalTensorSquare.sg958)

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

lemma sg958 : RowSquare [5,3,1,1] [2,2,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
