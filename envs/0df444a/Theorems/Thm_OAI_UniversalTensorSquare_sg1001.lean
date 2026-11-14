-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg1001
-- name    : OAI.UniversalTensorSquare.sg1001
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-13T13:06:50.325201+00:00
-- url     : https://prove2.me/theorems/0d80fbec-f33c-4895-956c-50a7f70396eb
-- title:
--   OAI.UniversalTensorSquare.sg1001: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg1001` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg1001 : RowSquare [6,1,1,1,1] [2,2,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_126All`, `OAI.UniversalTensorSquare.degreeTree43_143All`, `OAI.UniversalTensorSquare.degreeTree43_151All`, `OAI.UniversalTensorSquare.degreeTree43_194All`, `OAI.UniversalTensorSquare.degreeTree43_205All`, `OAI.UniversalTensorSquare.degreeTree43_238All`, `OAI.UniversalTensorSquare.degreeTree43_242All`, `OAI.UniversalTensorSquare.degreeTree43_24All`, `OAI.UniversalTensorSquare.degreeTree43_394All`, `OAI.UniversalTensorSquare.degreeTree43_425All`, `OAI.UniversalTensorSquare.degreeTree43_43All`, `OAI.UniversalTensorSquare.degreeTree43_488All`, `OAI.UniversalTensorSquare.degreeTree43_583All`, `OAI.UniversalTensorSquare.degreeTree43_593All`, `OAI.UniversalTensorSquare.degreeTree43_59All`, `OAI.UniversalTensorSquare.degreeTree43_80All`, `OAI.UniversalTensorSquare.degreeTree43_82All`, `OAI.UniversalTensorSquare.degreeTree58_1All`, `OAI.UniversalTensorSquare.degreeTree62_1000All`, `OAI.UniversalTensorSquare.degreeTree62_1004All`, `OAI.UniversalTensorSquare.degreeTree62_120All`, `OAI.UniversalTensorSquare.degreeTree62_122All`, `OAI.UniversalTensorSquare.degreeTree62_147All`, `OAI.UniversalTensorSquare.degreeTree62_150All`, `OAI.UniversalTensorSquare.degreeTree62_155All`, `OAI.UniversalTensorSquare.degreeTree62_166All`, `OAI.UniversalTensorSquare.degreeTree62_371All`, `OAI.UniversalTensorSquare.degreeTree62_38All`, `OAI.UniversalTensorSquare.degreeTree62_503All`, `OAI.UniversalTensorSquare.degreeTree62_50All`, `OAI.UniversalTensorSquare.degreeTree62_521All`, `OAI.UniversalTensorSquare.degreeTree62_56All`, `OAI.UniversalTensorSquare.degreeTree62_57All`, `OAI.UniversalTensorSquare.degreeTree62_617All`, `OAI.UniversalTensorSquare.degreeTree62_77All`, `OAI.UniversalTensorSquare.degreeTree62_822All`, `OAI.UniversalTensorSquare.degreeTree62_823All`, `OAI.UniversalTensorSquare.degreeTree62_847All`, `OAI.UniversalTensorSquare.degreeTree62_857All`, `OAI.UniversalTensorSquare.degreeTree62_891All`, `OAI.UniversalTensorSquare.degreeTree62_94All`, `OAI.UniversalTensorSquare.sg16139`, `OAI.UniversalTensorSquare.sg23739`, `OAI.UniversalTensorSquare.sg25616`, `OAI.UniversalTensorSquare.sg25893`, `OAI.UniversalTensorSquare.sg6942` and `OAI.UniversalTensorSquare.sg9752` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean (declaration OAI.UniversalTensorSquare.sg1001)

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

lemma sg1001 : RowSquare [6,1,1,1,1] [2,2,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
