-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg16690
-- name    : OAI.UniversalTensorSquare.sg16690
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:27:54.826203+00:00
-- url     : https://prove2.me/theorems/922576ff-754b-49dd-b221-470bdea1cf1b
-- title:
--   OAI.UniversalTensorSquare.sg16690: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg16690` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes40.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes40.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg16690 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,6,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_20All`, `OAI.UniversalTensorSquare.degreeTree62_309All`, `OAI.UniversalTensorSquare.degreeTree62_38All`, `OAI.UniversalTensorSquare.degreeTree62_4All`, `OAI.UniversalTensorSquare.degreeTree62_72All`, `OAI.UniversalTensorSquare.sg32713`, `OAI.UniversalTensorSquare.sg33068`, `OAI.UniversalTensorSquare.sg33069`, `OAI.UniversalTensorSquare.sg33070`, `OAI.UniversalTensorSquare.sg33413`, `OAI.UniversalTensorSquare.sg34607`, `OAI.UniversalTensorSquare.sg37706` and `OAI.UniversalTensorSquare.sg37707` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes40.lean (declaration OAI.UniversalTensorSquare.sg16690)

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

lemma sg16690 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,6,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
