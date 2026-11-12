-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg16382
-- name    : OAI.UniversalTensorSquare.sg16382
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:25:43.882004+00:00
-- url     : https://prove2.me/theorems/fa815a11-df57-4836-852d-fb677be63332
-- title:
--   OAI.UniversalTensorSquare.sg16382: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg16382` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes39.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes39.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg16382 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,7,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_127All`, `OAI.UniversalTensorSquare.degreeTree62_216All`, `OAI.UniversalTensorSquare.degreeTree62_253All`, `OAI.UniversalTensorSquare.degreeTree62_304All`, `OAI.UniversalTensorSquare.degreeTree62_306All` and `OAI.UniversalTensorSquare.sg35400` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes39.lean (declaration OAI.UniversalTensorSquare.sg16382)

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

lemma sg16382 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,7,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
