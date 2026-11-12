-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg15756
-- name    : OAI.UniversalTensorSquare.sg15756
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:23:06.892578+00:00
-- url     : https://prove2.me/theorems/98d2cf5e-c811-4223-ae64-f4ede1df98d1
-- title:
--   OAI.UniversalTensorSquare.sg15756: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg15756` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes38.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes38.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg15756 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,6]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_121All`, `OAI.UniversalTensorSquare.degreeTree62_515All`, `OAI.UniversalTensorSquare.degreeTree62_625All`, `OAI.UniversalTensorSquare.degreeTree62_722All`, `OAI.UniversalTensorSquare.degreeTree62_72All`, `OAI.UniversalTensorSquare.degreeTree62_89All`, `OAI.UniversalTensorSquare.sg38909` and `OAI.UniversalTensorSquare.sg41499` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes38.lean (declaration OAI.UniversalTensorSquare.sg15756)

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

lemma sg15756 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,6] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
