-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg358
-- name    : OAI.UniversalTensorSquare.sg358
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T11:57:49.195714+00:00
-- url     : https://prove2.me/theorems/72c29ca0-0b48-4970-8b39-733509c0d794
-- title:
--   OAI.UniversalTensorSquare.sg358: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg358` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg358 : RowSquare [4,3,1] [2,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_42All`, `OAI.UniversalTensorSquare.degreeTree62_220All`, `OAI.UniversalTensorSquare.degreeTree62_47All`, `OAI.UniversalTensorSquare.degreeTree62_503All`, `OAI.UniversalTensorSquare.degreeTree62_607All`, `OAI.UniversalTensorSquare.degreeTree62_615All`, `OAI.UniversalTensorSquare.degreeTree62_617All`, `OAI.UniversalTensorSquare.degreeTree62_699All`, `OAI.UniversalTensorSquare.degreeTree62_706All`, `OAI.UniversalTensorSquare.degreeTree62_786All`, `OAI.UniversalTensorSquare.degreeTree62_854All`, `OAI.UniversalTensorSquare.degreeTree62_913All`, `OAI.UniversalTensorSquare.sg34488`, `OAI.UniversalTensorSquare.sg37390`, `OAI.UniversalTensorSquare.sg37606`, `OAI.UniversalTensorSquare.sg37632`, `OAI.UniversalTensorSquare.sg38874`, `OAI.UniversalTensorSquare.sg39916`, `OAI.UniversalTensorSquare.sg41456`, `OAI.UniversalTensorSquare.sg41467`, `OAI.UniversalTensorSquare.sg41474`, `OAI.UniversalTensorSquare.sg41478`, `OAI.UniversalTensorSquare.sg41483`, `OAI.UniversalTensorSquare.sg42078` and `OAI.UniversalTensorSquare.sg43199` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean (declaration OAI.UniversalTensorSquare.sg358)

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

lemma sg358 : RowSquare [4,3,1] [2,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
