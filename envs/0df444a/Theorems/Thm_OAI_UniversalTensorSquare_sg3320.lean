-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg3320
-- name    : OAI.UniversalTensorSquare.sg3320
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T09:22:33.353885+00:00
-- url     : https://prove2.me/theorems/2771893a-c8b1-4663-b2f2-2dd6f26399bc
-- title:
--   OAI.UniversalTensorSquare.sg3320: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg3320` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg3320 : RowSquare [6,3,3,1,1,1] [2,2,1,1,1,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_542All`, `OAI.UniversalTensorSquare.degreeTree62_574All`, `OAI.UniversalTensorSquare.degreeTree62_723All`, `OAI.UniversalTensorSquare.degreeTree62_922All`, `OAI.UniversalTensorSquare.degreeTree62_956All`, `OAI.UniversalTensorSquare.degreeTree62_958All`, `OAI.UniversalTensorSquare.degreeTree62_967All`, `OAI.UniversalTensorSquare.sg18284`, `OAI.UniversalTensorSquare.sg33640`, `OAI.UniversalTensorSquare.sg33653`, `OAI.UniversalTensorSquare.sg34087`, `OAI.UniversalTensorSquare.sg34248`, `OAI.UniversalTensorSquare.sg34483`, `OAI.UniversalTensorSquare.sg34508`, `OAI.UniversalTensorSquare.sg34533`, `OAI.UniversalTensorSquare.sg37053`, `OAI.UniversalTensorSquare.sg38384`, `OAI.UniversalTensorSquare.sg38595`, `OAI.UniversalTensorSquare.sg38988`, `OAI.UniversalTensorSquare.sg39184`, `OAI.UniversalTensorSquare.sg39374`, `OAI.UniversalTensorSquare.sg39545`, `OAI.UniversalTensorSquare.sg39998`, `OAI.UniversalTensorSquare.sg40046`, `OAI.UniversalTensorSquare.sg40073`, `OAI.UniversalTensorSquare.sg40180`, `OAI.UniversalTensorSquare.sg40211`, `OAI.UniversalTensorSquare.sg40220`, `OAI.UniversalTensorSquare.sg40947`, `OAI.UniversalTensorSquare.sg41158`, `OAI.UniversalTensorSquare.sg41179`, `OAI.UniversalTensorSquare.sg41542`, `OAI.UniversalTensorSquare.sg41650`, `OAI.UniversalTensorSquare.sg41851`, `OAI.UniversalTensorSquare.sg42368`, `OAI.UniversalTensorSquare.sg42646` and `OAI.UniversalTensorSquare.sg42662` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean (declaration OAI.UniversalTensorSquare.sg3320)

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

lemma sg3320 : RowSquare [6,3,3,1,1,1] [2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
