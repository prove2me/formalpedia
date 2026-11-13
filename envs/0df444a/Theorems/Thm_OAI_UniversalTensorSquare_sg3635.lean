-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg3635
-- name    : OAI.UniversalTensorSquare.sg3635
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T15:59:34.867849+00:00
-- url     : https://prove2.me/theorems/e7700d9c-9306-43b9-a61a-e9bdbac57997
-- title:
--   OAI.UniversalTensorSquare.sg3635: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg3635` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg3635 : RowSquare [8,3,2,2] [3,3,2,2,2,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_163All`, `OAI.UniversalTensorSquare.degreeTree62_341All`, `OAI.UniversalTensorSquare.degreeTree62_404All`, `OAI.UniversalTensorSquare.degreeTree62_427All`, `OAI.UniversalTensorSquare.degreeTree62_475All`, `OAI.UniversalTensorSquare.degreeTree62_530All`, `OAI.UniversalTensorSquare.degreeTree62_534All`, `OAI.UniversalTensorSquare.degreeTree62_547All`, `OAI.UniversalTensorSquare.degreeTree62_550All`, `OAI.UniversalTensorSquare.degreeTree62_566All`, `OAI.UniversalTensorSquare.degreeTree62_567All`, `OAI.UniversalTensorSquare.degreeTree62_583All`, `OAI.UniversalTensorSquare.degreeTree62_642All`, `OAI.UniversalTensorSquare.degreeTree62_654All`, `OAI.UniversalTensorSquare.degreeTree62_662All`, `OAI.UniversalTensorSquare.degreeTree62_670All`, `OAI.UniversalTensorSquare.degreeTree62_685All`, `OAI.UniversalTensorSquare.degreeTree62_693All`, `OAI.UniversalTensorSquare.degreeTree62_736All`, `OAI.UniversalTensorSquare.degreeTree62_742All`, `OAI.UniversalTensorSquare.sg36540`, `OAI.UniversalTensorSquare.sg37803`, `OAI.UniversalTensorSquare.sg38144`, `OAI.UniversalTensorSquare.sg38513`, `OAI.UniversalTensorSquare.sg38626`, `OAI.UniversalTensorSquare.sg38952`, `OAI.UniversalTensorSquare.sg39017`, `OAI.UniversalTensorSquare.sg39129`, `OAI.UniversalTensorSquare.sg39344`, `OAI.UniversalTensorSquare.sg39435`, `OAI.UniversalTensorSquare.sg39678`, `OAI.UniversalTensorSquare.sg39770`, `OAI.UniversalTensorSquare.sg40021`, `OAI.UniversalTensorSquare.sg40193`, `OAI.UniversalTensorSquare.sg40450`, `OAI.UniversalTensorSquare.sg40841`, `OAI.UniversalTensorSquare.sg40879`, `OAI.UniversalTensorSquare.sg41048`, `OAI.UniversalTensorSquare.sg41106`, `OAI.UniversalTensorSquare.sg41524`, `OAI.UniversalTensorSquare.sg41560`, `OAI.UniversalTensorSquare.sg41621`, `OAI.UniversalTensorSquare.sg41715`, `OAI.UniversalTensorSquare.sg41740`, `OAI.UniversalTensorSquare.sg41775`, `OAI.UniversalTensorSquare.sg41794`, `OAI.UniversalTensorSquare.sg41876`, `OAI.UniversalTensorSquare.sg41909`, `OAI.UniversalTensorSquare.sg42106`, `OAI.UniversalTensorSquare.sg42139`, `OAI.UniversalTensorSquare.sg42166` and `OAI.UniversalTensorSquare.sg42187` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean (declaration OAI.UniversalTensorSquare.sg3635)

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

lemma sg3635 : RowSquare [8,3,2,2] [3,3,2,2,2,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
