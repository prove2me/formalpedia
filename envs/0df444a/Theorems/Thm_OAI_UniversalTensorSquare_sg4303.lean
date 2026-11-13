-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg4303
-- name    : OAI.UniversalTensorSquare.sg4303
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T21:35:09.020236+00:00
-- url     : https://prove2.me/theorems/95b11755-a6c7-45ee-abc6-622ae2f74e2d
-- title:
--   OAI.UniversalTensorSquare.sg4303: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg4303` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg4303 : RowSquare [7,4,2,1,1,1] [3,3,3,3,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_12All`, `OAI.UniversalTensorSquare.degreeTree62_155All`, `OAI.UniversalTensorSquare.degreeTree62_212All`, `OAI.UniversalTensorSquare.degreeTree62_385All`, `OAI.UniversalTensorSquare.degreeTree62_502All`, `OAI.UniversalTensorSquare.sg32056`, `OAI.UniversalTensorSquare.sg32220`, `OAI.UniversalTensorSquare.sg32372`, `OAI.UniversalTensorSquare.sg32374`, `OAI.UniversalTensorSquare.sg32386`, `OAI.UniversalTensorSquare.sg32388`, `OAI.UniversalTensorSquare.sg32390`, `OAI.UniversalTensorSquare.sg32392`, `OAI.UniversalTensorSquare.sg32628`, `OAI.UniversalTensorSquare.sg32636`, `OAI.UniversalTensorSquare.sg32638`, `OAI.UniversalTensorSquare.sg32641`, `OAI.UniversalTensorSquare.sg32672`, `OAI.UniversalTensorSquare.sg32673`, `OAI.UniversalTensorSquare.sg32674`, `OAI.UniversalTensorSquare.sg32676`, `OAI.UniversalTensorSquare.sg32677`, `OAI.UniversalTensorSquare.sg32998`, `OAI.UniversalTensorSquare.sg33588`, `OAI.UniversalTensorSquare.sg37615` and `OAI.UniversalTensorSquare.sg40738` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean (declaration OAI.UniversalTensorSquare.sg4303)

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

lemma sg4303 : RowSquare [7,4,2,1,1,1] [3,3,3,3,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
