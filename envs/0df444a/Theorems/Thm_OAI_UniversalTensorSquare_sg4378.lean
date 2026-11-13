-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg4378
-- name    : OAI.UniversalTensorSquare.sg4378
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:00:00.312101+00:00
-- url     : https://prove2.me/theorems/6406d1c6-8f19-4d10-ba9f-543957374c93
-- title:
--   OAI.UniversalTensorSquare.sg4378: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg4378` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg4378 : RowSquare [8,3,2,1,1,1] [3,3,3,3,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_12All`, `OAI.UniversalTensorSquare.degreeTree62_229All`, `OAI.UniversalTensorSquare.degreeTree62_2All`, `OAI.UniversalTensorSquare.degreeTree62_306All`, `OAI.UniversalTensorSquare.degreeTree62_307All`, `OAI.UniversalTensorSquare.degreeTree62_310All`, `OAI.UniversalTensorSquare.degreeTree62_384All`, `OAI.UniversalTensorSquare.degreeTree62_3All`, `OAI.UniversalTensorSquare.degreeTree62_55All`, `OAI.UniversalTensorSquare.degreeTree62_75All`, `OAI.UniversalTensorSquare.sg31987`, `OAI.UniversalTensorSquare.sg32060`, `OAI.UniversalTensorSquare.sg32222`, `OAI.UniversalTensorSquare.sg32223`, `OAI.UniversalTensorSquare.sg32578`, `OAI.UniversalTensorSquare.sg32579`, `OAI.UniversalTensorSquare.sg32580`, `OAI.UniversalTensorSquare.sg32626`, `OAI.UniversalTensorSquare.sg32627`, `OAI.UniversalTensorSquare.sg32637`, `OAI.UniversalTensorSquare.sg32639`, `OAI.UniversalTensorSquare.sg32678`, `OAI.UniversalTensorSquare.sg32745`, `OAI.UniversalTensorSquare.sg32813`, `OAI.UniversalTensorSquare.sg32992`, `OAI.UniversalTensorSquare.sg32994`, `OAI.UniversalTensorSquare.sg33398`, `OAI.UniversalTensorSquare.sg33997`, `OAI.UniversalTensorSquare.sg34596`, `OAI.UniversalTensorSquare.sg35458` and `OAI.UniversalTensorSquare.sg37652` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean (declaration OAI.UniversalTensorSquare.sg4378)

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

lemma sg4378 : RowSquare [8,3,2,1,1,1] [3,3,3,3,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
