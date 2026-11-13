-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg4489
-- name    : OAI.UniversalTensorSquare.sg4489
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:15:48.909961+00:00
-- url     : https://prove2.me/theorems/0eca3a5b-1b9c-4d89-8db9-4445b66c2397
-- title:
--   OAI.UniversalTensorSquare.sg4489: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg4489` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg4489 : RowSquare [9,3,2,1,1] [3,3,3,3,3,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_157All`, `OAI.UniversalTensorSquare.degreeTree62_16All`, `OAI.UniversalTensorSquare.degreeTree62_395All`, `OAI.UniversalTensorSquare.degreeTree62_81All`, `OAI.UniversalTensorSquare.sg31967`, `OAI.UniversalTensorSquare.sg31968`, `OAI.UniversalTensorSquare.sg32192`, `OAI.UniversalTensorSquare.sg32196`, `OAI.UniversalTensorSquare.sg32198`, `OAI.UniversalTensorSquare.sg32251`, `OAI.UniversalTensorSquare.sg32296`, `OAI.UniversalTensorSquare.sg32670`, `OAI.UniversalTensorSquare.sg33653`, `OAI.UniversalTensorSquare.sg33657`, `OAI.UniversalTensorSquare.sg33659`, `OAI.UniversalTensorSquare.sg33989`, `OAI.UniversalTensorSquare.sg36300`, `OAI.UniversalTensorSquare.sg36303`, `OAI.UniversalTensorSquare.sg36322`, `OAI.UniversalTensorSquare.sg36329`, `OAI.UniversalTensorSquare.sg37052`, `OAI.UniversalTensorSquare.sg37054`, `OAI.UniversalTensorSquare.sg37058`, `OAI.UniversalTensorSquare.sg37061`, `OAI.UniversalTensorSquare.sg37501`, `OAI.UniversalTensorSquare.sg37502`, `OAI.UniversalTensorSquare.sg37503`, `OAI.UniversalTensorSquare.sg37505`, `OAI.UniversalTensorSquare.sg37687`, `OAI.UniversalTensorSquare.sg37709`, `OAI.UniversalTensorSquare.sg37710`, `OAI.UniversalTensorSquare.sg37712`, `OAI.UniversalTensorSquare.sg37713`, `OAI.UniversalTensorSquare.sg41179` and `OAI.UniversalTensorSquare.sg41842` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean (declaration OAI.UniversalTensorSquare.sg4489)

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

lemma sg4489 : RowSquare [9,3,2,1,1] [3,3,3,3,3,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
