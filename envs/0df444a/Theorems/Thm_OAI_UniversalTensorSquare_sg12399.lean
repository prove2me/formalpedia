-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg12399
-- name    : OAI.UniversalTensorSquare.sg12399
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T20:55:42.377197+00:00
-- url     : https://prove2.me/theorems/4e1cd2bb-a887-4052-8835-e09061270f6a
-- title:
--   OAI.UniversalTensorSquare.sg12399: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg12399` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes29.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes29.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg12399 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,3,3,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_821All`, `OAI.UniversalTensorSquare.degreeTree62_899All`, `OAI.UniversalTensorSquare.sg41959`, `OAI.UniversalTensorSquare.sg43113` and `OAI.UniversalTensorSquare.sg43120` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes29.lean (declaration OAI.UniversalTensorSquare.sg12399)

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

lemma sg12399 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,3,3,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
