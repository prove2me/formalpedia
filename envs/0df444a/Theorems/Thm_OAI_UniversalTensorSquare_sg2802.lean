-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg2802
-- name    : OAI.UniversalTensorSquare.sg2802
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T07:17:57.743797+00:00
-- url     : https://prove2.me/theorems/7301fc15-44e4-4f19-be7e-fa64d0b3888c
-- title:
--   OAI.UniversalTensorSquare.sg2802: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg2802` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg2802 : RowSquare [7,4,2,1] [3,3,2,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_151All`, `OAI.UniversalTensorSquare.degreeTree62_152All`, `OAI.UniversalTensorSquare.degreeTree62_155All`, `OAI.UniversalTensorSquare.degreeTree62_173All`, `OAI.UniversalTensorSquare.degreeTree62_176All`, `OAI.UniversalTensorSquare.degreeTree62_667All`, `OAI.UniversalTensorSquare.degreeTree62_746All`, `OAI.UniversalTensorSquare.degreeTree62_973All`, `OAI.UniversalTensorSquare.sg16747`, `OAI.UniversalTensorSquare.sg32146`, `OAI.UniversalTensorSquare.sg33740`, `OAI.UniversalTensorSquare.sg33957`, `OAI.UniversalTensorSquare.sg39159`, `OAI.UniversalTensorSquare.sg39163`, `OAI.UniversalTensorSquare.sg39165`, `OAI.UniversalTensorSquare.sg39327`, `OAI.UniversalTensorSquare.sg39333`, `OAI.UniversalTensorSquare.sg40105`, `OAI.UniversalTensorSquare.sg40219`, `OAI.UniversalTensorSquare.sg40223`, `OAI.UniversalTensorSquare.sg42590`, `OAI.UniversalTensorSquare.sg42735` and `OAI.UniversalTensorSquare.sg42778` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes5.lean (declaration OAI.UniversalTensorSquare.sg2802)

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

lemma sg2802 : RowSquare [7,4,2,1] [3,3,2,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
