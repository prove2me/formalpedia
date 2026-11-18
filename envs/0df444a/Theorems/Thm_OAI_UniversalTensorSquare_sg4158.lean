-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg4158
-- name    : OAI.UniversalTensorSquare.sg4158
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T20:14:47.100732+00:00
-- url     : https://prove2.me/theorems/d79e6b92-51c7-4d18-9027-2d551ef8edd0
-- title:
--   OAI.UniversalTensorSquare.sg4158: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg4158` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg4158 : RowSquare [7,3,1,1,1,1,1,1] [4,3,3,3,3]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg19628`, `OAI.UniversalTensorSquare.sg32770`, `OAI.UniversalTensorSquare.sg32823`, `OAI.UniversalTensorSquare.sg37019`, `OAI.UniversalTensorSquare.sg37020`, `OAI.UniversalTensorSquare.sg37022`, `OAI.UniversalTensorSquare.sg37023`, `OAI.UniversalTensorSquare.sg37025`, `OAI.UniversalTensorSquare.sg37027`, `OAI.UniversalTensorSquare.sg37030` and `OAI.UniversalTensorSquare.sg38752` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean (declaration OAI.UniversalTensorSquare.sg4158)

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

lemma sg4158 : RowSquare [7,3,1,1,1,1,1,1] [4,3,3,3,3] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
