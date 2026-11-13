-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg3012
-- name    : OAI.UniversalTensorSquare.sg3012
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T09:40:10.911241+00:00
-- url     : https://prove2.me/theorems/a204af24-873f-492d-a96a-fd78e2881403
-- title:
--   OAI.UniversalTensorSquare.sg3012: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg3012` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes6.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes6.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg3012 : RowSquare [8,3,2,1] [4,2,2,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_367All`, `OAI.UniversalTensorSquare.degreeTree62_385All`, `OAI.UniversalTensorSquare.degreeTree62_490All`, `OAI.UniversalTensorSquare.degreeTree62_65All`, `OAI.UniversalTensorSquare.degreeTree62_72All`, `OAI.UniversalTensorSquare.sg17423`, `OAI.UniversalTensorSquare.sg32801`, `OAI.UniversalTensorSquare.sg36180`, `OAI.UniversalTensorSquare.sg36247`, `OAI.UniversalTensorSquare.sg36248`, `OAI.UniversalTensorSquare.sg36272`, `OAI.UniversalTensorSquare.sg36578`, `OAI.UniversalTensorSquare.sg36603`, `OAI.UniversalTensorSquare.sg36761`, `OAI.UniversalTensorSquare.sg36845`, `OAI.UniversalTensorSquare.sg36932`, `OAI.UniversalTensorSquare.sg37292`, `OAI.UniversalTensorSquare.sg37955`, `OAI.UniversalTensorSquare.sg37972`, `OAI.UniversalTensorSquare.sg38133`, `OAI.UniversalTensorSquare.sg38198`, `OAI.UniversalTensorSquare.sg40512`, `OAI.UniversalTensorSquare.sg40651`, `OAI.UniversalTensorSquare.sg40652`, `OAI.UniversalTensorSquare.sg40702`, `OAI.UniversalTensorSquare.sg41079`, `OAI.UniversalTensorSquare.sg41316`, `OAI.UniversalTensorSquare.sg41646`, `OAI.UniversalTensorSquare.sg42822`, `OAI.UniversalTensorSquare.sg42845`, `OAI.UniversalTensorSquare.sg42847` and `OAI.UniversalTensorSquare.sg42899` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes6.lean (declaration OAI.UniversalTensorSquare.sg3012)

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

lemma sg3012 : RowSquare [8,3,2,1] [4,2,2,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
