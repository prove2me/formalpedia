-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg377
-- name    : OAI.UniversalTensorSquare.sg377
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T14:53:38.382197+00:00
-- url     : https://prove2.me/theorems/f930973b-c8e4-4bbc-964b-fc77f09e1195
-- title:
--   OAI.UniversalTensorSquare.sg377: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg377` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg377 : RowSquare [5,1,1,1] [3,3,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_215All`, `OAI.UniversalTensorSquare.degreeTree43_507All`, `OAI.UniversalTensorSquare.degreeTree43_635All`, `OAI.UniversalTensorSquare.degreeTree62_932All`, `OAI.UniversalTensorSquare.degreeTree62_967All`, `OAI.UniversalTensorSquare.degreeTree62_974All`, `OAI.UniversalTensorSquare.sg20006`, `OAI.UniversalTensorSquare.sg26367`, `OAI.UniversalTensorSquare.sg26437`, `OAI.UniversalTensorSquare.sg29263`, `OAI.UniversalTensorSquare.sg30181`, `OAI.UniversalTensorSquare.sg30232`, `OAI.UniversalTensorSquare.sg31578`, `OAI.UniversalTensorSquare.sg31590`, `OAI.UniversalTensorSquare.sg31592`, `OAI.UniversalTensorSquare.sg31732`, `OAI.UniversalTensorSquare.sg31884`, `OAI.UniversalTensorSquare.sg37958`, `OAI.UniversalTensorSquare.sg39415`, `OAI.UniversalTensorSquare.sg41731`, `OAI.UniversalTensorSquare.sg41762`, `OAI.UniversalTensorSquare.sg42323`, `OAI.UniversalTensorSquare.sg42673`, `OAI.UniversalTensorSquare.sg42710`, `OAI.UniversalTensorSquare.sg42751`, `OAI.UniversalTensorSquare.sg43041`, `OAI.UniversalTensorSquare.sg5397`, `OAI.UniversalTensorSquare.sg5632`, `OAI.UniversalTensorSquare.sg6891`, `OAI.UniversalTensorSquare.sg7212` and `OAI.UniversalTensorSquare.sg9981` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean (declaration OAI.UniversalTensorSquare.sg377)

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

lemma sg377 : RowSquare [5,1,1,1] [3,3,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
