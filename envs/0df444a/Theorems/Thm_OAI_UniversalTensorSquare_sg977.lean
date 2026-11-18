-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg977
-- name    : OAI.UniversalTensorSquare.sg977
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-18T00:07:57.607415+00:00
-- url     : https://prove2.me/theorems/24d87e20-7378-4756-ae80-ae4de9631407
-- title:
--   OAI.UniversalTensorSquare.sg977: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg977` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg977 : RowSquare [5,3,2] [2,2,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_1010All`, `OAI.UniversalTensorSquare.degreeTree62_59All`, `OAI.UniversalTensorSquare.degreeTree62_829All`, `OAI.UniversalTensorSquare.degreeTree62_851All`, `OAI.UniversalTensorSquare.sg16333`, `OAI.UniversalTensorSquare.sg31973`, `OAI.UniversalTensorSquare.sg35467`, `OAI.UniversalTensorSquare.sg37410`, `OAI.UniversalTensorSquare.sg37662`, `OAI.UniversalTensorSquare.sg37665`, `OAI.UniversalTensorSquare.sg38287`, `OAI.UniversalTensorSquare.sg38558`, `OAI.UniversalTensorSquare.sg38745`, `OAI.UniversalTensorSquare.sg40751`, `OAI.UniversalTensorSquare.sg41293`, `OAI.UniversalTensorSquare.sg41406`, `OAI.UniversalTensorSquare.sg41491`, `OAI.UniversalTensorSquare.sg41736`, `OAI.UniversalTensorSquare.sg41832`, `OAI.UniversalTensorSquare.sg41834`, `OAI.UniversalTensorSquare.sg42024`, `OAI.UniversalTensorSquare.sg42081`, `OAI.UniversalTensorSquare.sg42082`, `OAI.UniversalTensorSquare.sg42183`, `OAI.UniversalTensorSquare.sg42546`, `OAI.UniversalTensorSquare.sg43003`, `OAI.UniversalTensorSquare.sg43119` and `OAI.UniversalTensorSquare.sg43219` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean (declaration OAI.UniversalTensorSquare.sg977)

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

lemma sg977 : RowSquare [5,3,2] [2,2,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
