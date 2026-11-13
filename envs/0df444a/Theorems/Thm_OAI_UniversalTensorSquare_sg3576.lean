-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg3576
-- name    : OAI.UniversalTensorSquare.sg3576
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T15:37:32.642681+00:00
-- url     : https://prove2.me/theorems/464d01d8-5157-4d2a-b4cb-f1f3df226b6c
-- title:
--   OAI.UniversalTensorSquare.sg3576: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg3576` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg3576 : RowSquare [8,3,1,1,1,1] [3,3,3,2,2,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_102All`, `OAI.UniversalTensorSquare.degreeTree62_182All`, `OAI.UniversalTensorSquare.degreeTree62_249All`, `OAI.UniversalTensorSquare.degreeTree62_258All`, `OAI.UniversalTensorSquare.degreeTree62_262All`, `OAI.UniversalTensorSquare.degreeTree62_263All`, `OAI.UniversalTensorSquare.degreeTree62_274All`, `OAI.UniversalTensorSquare.degreeTree62_279All`, `OAI.UniversalTensorSquare.degreeTree62_357All`, `OAI.UniversalTensorSquare.degreeTree62_434All`, `OAI.UniversalTensorSquare.degreeTree62_478All`, `OAI.UniversalTensorSquare.degreeTree62_494All`, `OAI.UniversalTensorSquare.degreeTree62_604All`, `OAI.UniversalTensorSquare.degreeTree62_80All`, `OAI.UniversalTensorSquare.sg17542`, `OAI.UniversalTensorSquare.sg19110`, `OAI.UniversalTensorSquare.sg19114`, `OAI.UniversalTensorSquare.sg19128`, `OAI.UniversalTensorSquare.sg19133`, `OAI.UniversalTensorSquare.sg33172`, `OAI.UniversalTensorSquare.sg33374`, `OAI.UniversalTensorSquare.sg34036`, `OAI.UniversalTensorSquare.sg34037`, `OAI.UniversalTensorSquare.sg34038`, `OAI.UniversalTensorSquare.sg34046`, `OAI.UniversalTensorSquare.sg36747`, `OAI.UniversalTensorSquare.sg37219`, `OAI.UniversalTensorSquare.sg37222`, `OAI.UniversalTensorSquare.sg37430`, `OAI.UniversalTensorSquare.sg38721` and `OAI.UniversalTensorSquare.sg41068` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean (declaration OAI.UniversalTensorSquare.sg3576)

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

lemma sg3576 : RowSquare [8,3,1,1,1,1] [3,3,3,2,2,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
