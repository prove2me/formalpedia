-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg13840
-- name    : OAI.UniversalTensorSquare.sg13840
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:16:05.556895+00:00
-- url     : https://prove2.me/theorems/0234e537-5061-480a-bd4c-9099cacb9069
-- title:
--   OAI.UniversalTensorSquare.sg13840: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg13840` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes33.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes33.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg13840 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,4,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_569All`, `OAI.UniversalTensorSquare.degreeTree62_677All`, `OAI.UniversalTensorSquare.degreeTree62_709All`, `OAI.UniversalTensorSquare.degreeTree62_719All`, `OAI.UniversalTensorSquare.degreeTree62_722All`, `OAI.UniversalTensorSquare.sg38318`, `OAI.UniversalTensorSquare.sg39142`, `OAI.UniversalTensorSquare.sg42195` and `OAI.UniversalTensorSquare.sg42639` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes33.lean (declaration OAI.UniversalTensorSquare.sg13840)

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

lemma sg13840 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,4,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
