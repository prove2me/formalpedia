-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg1687
-- name    : OAI.UniversalTensorSquare.sg1687
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:29:26.285744+00:00
-- url     : https://prove2.me/theorems/e23342fd-2ca6-4936-a1cd-ac3d11ee5049
-- title:
--   OAI.UniversalTensorSquare.sg1687: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg1687` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg1687 : RowSquare [5,3,2,1,1] [2,2,2,2,2,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_122All`, `OAI.UniversalTensorSquare.degreeTree43_24All`, `OAI.UniversalTensorSquare.degreeTree43_56All`, `OAI.UniversalTensorSquare.degreeTree43_75All`, `OAI.UniversalTensorSquare.degreeTree62_494All`, `OAI.UniversalTensorSquare.degreeTree62_518All`, `OAI.UniversalTensorSquare.degreeTree62_67All`, `OAI.UniversalTensorSquare.degreeTreeAll16`, `OAI.UniversalTensorSquare.sg23973`, `OAI.UniversalTensorSquare.sg24210`, `OAI.UniversalTensorSquare.sg25653`, `OAI.UniversalTensorSquare.sg31982`, `OAI.UniversalTensorSquare.sg37046`, `OAI.UniversalTensorSquare.sg38358` and `OAI.UniversalTensorSquare.sg38369` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes3.lean (declaration OAI.UniversalTensorSquare.sg1687)

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

lemma sg1687 : RowSquare [5,3,2,1,1] [2,2,2,2,2,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
