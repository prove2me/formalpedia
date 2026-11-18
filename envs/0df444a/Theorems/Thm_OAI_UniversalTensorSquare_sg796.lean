-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg796
-- name    : OAI.UniversalTensorSquare.sg796
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T23:28:07.841094+00:00
-- url     : https://prove2.me/theorems/357f8710-f097-460c-b0c9-8ac93f83c574
-- title:
--   OAI.UniversalTensorSquare.sg796: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg796` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg796 : RowSquare [3,3,2,2] [2,2,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree58_0All`, `OAI.UniversalTensorSquare.degreeTree62_34All`, `OAI.UniversalTensorSquare.degreeTree62_388All`, `OAI.UniversalTensorSquare.degreeTree62_452All`, `OAI.UniversalTensorSquare.degreeTree62_471All`, `OAI.UniversalTensorSquare.sg31956`, `OAI.UniversalTensorSquare.sg31964`, `OAI.UniversalTensorSquare.sg31985`, `OAI.UniversalTensorSquare.sg31990`, `OAI.UniversalTensorSquare.sg31992`, `OAI.UniversalTensorSquare.sg31995`, `OAI.UniversalTensorSquare.sg32305`, `OAI.UniversalTensorSquare.sg32822`, `OAI.UniversalTensorSquare.sg34675`, `OAI.UniversalTensorSquare.sg36278`, `OAI.UniversalTensorSquare.sg37017`, `OAI.UniversalTensorSquare.sg37037`, `OAI.UniversalTensorSquare.sg37249`, `OAI.UniversalTensorSquare.sg40754` and `OAI.UniversalTensorSquare.sg40767` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean (declaration OAI.UniversalTensorSquare.sg796)

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

lemma sg796 : RowSquare [3,3,2,2] [2,2,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
