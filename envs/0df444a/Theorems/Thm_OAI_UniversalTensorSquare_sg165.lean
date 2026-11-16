-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg165
-- name    : OAI.UniversalTensorSquare.sg165
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-16T02:40:47.869345+00:00
-- url     : https://prove2.me/theorems/0095ebde-05e8-4a88-a047-334fdc3065e4
-- title:
--   OAI.UniversalTensorSquare.sg165: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg165` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg165 : RowSquare [3,3,1] [2,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_534All`, `OAI.UniversalTensorSquare.degreeTree62_546All`, `OAI.UniversalTensorSquare.degreeTree62_581All`, `OAI.UniversalTensorSquare.degreeTree62_584All`, `OAI.UniversalTensorSquare.degreeTree62_662All`, `OAI.UniversalTensorSquare.degreeTree62_984All`, `OAI.UniversalTensorSquare.sg12716`, `OAI.UniversalTensorSquare.sg12717`, `OAI.UniversalTensorSquare.sg31978`, `OAI.UniversalTensorSquare.sg37173`, `OAI.UniversalTensorSquare.sg37358`, `OAI.UniversalTensorSquare.sg37923`, `OAI.UniversalTensorSquare.sg38101` and `OAI.UniversalTensorSquare.sg38240` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean (declaration OAI.UniversalTensorSquare.sg165)

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

lemma sg165 : RowSquare [3,3,1] [2,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
