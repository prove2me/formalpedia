-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg20713
-- name    : OAI.UniversalTensorSquare.sg20713
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:55:32.922477+00:00
-- url     : https://prove2.me/theorems/fd4de727-c064-4e4f-8dc3-88e24a011cbd
-- title:
--   OAI.UniversalTensorSquare.sg20713: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg20713` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes50.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes50.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg20713 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,4,4,3,3,3,2,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_510All`, `OAI.UniversalTensorSquare.degreeTree62_81All`, `OAI.UniversalTensorSquare.degreeTree62_852All`, `OAI.UniversalTensorSquare.sg33189`, `OAI.UniversalTensorSquare.sg37507`, `OAI.UniversalTensorSquare.sg38764`, `OAI.UniversalTensorSquare.sg39747`, `OAI.UniversalTensorSquare.sg39870`, `OAI.UniversalTensorSquare.sg41962`, `OAI.UniversalTensorSquare.sg42029`, `OAI.UniversalTensorSquare.sg42302`, `OAI.UniversalTensorSquare.sg42459` and `OAI.UniversalTensorSquare.sg42507` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes50.lean (declaration OAI.UniversalTensorSquare.sg20713)

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

lemma sg20713 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,4,4,3,3,3,2,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
