-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg20524
-- name    : OAI.UniversalTensorSquare.sg20524
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:51:59.091955+00:00
-- url     : https://prove2.me/theorems/55c926bf-8b19-48bc-a2ae-c600f9269fd1
-- title:
--   OAI.UniversalTensorSquare.sg20524: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg20524` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg20524 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,3,2,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_120All`, `OAI.UniversalTensorSquare.degreeTree62_137All`, `OAI.UniversalTensorSquare.degreeTree62_138All`, `OAI.UniversalTensorSquare.degreeTree62_13All`, `OAI.UniversalTensorSquare.degreeTree62_142All`, `OAI.UniversalTensorSquare.degreeTree62_176All`, `OAI.UniversalTensorSquare.degreeTree62_178All`, `OAI.UniversalTensorSquare.degreeTree62_201All`, `OAI.UniversalTensorSquare.degreeTree62_20All`, `OAI.UniversalTensorSquare.degreeTree62_216All`, `OAI.UniversalTensorSquare.degreeTree62_217All`, `OAI.UniversalTensorSquare.degreeTree62_229All`, `OAI.UniversalTensorSquare.degreeTree62_233All`, `OAI.UniversalTensorSquare.degreeTree62_263All`, `OAI.UniversalTensorSquare.degreeTree62_277All`, `OAI.UniversalTensorSquare.degreeTree62_279All`, `OAI.UniversalTensorSquare.degreeTree62_290All`, `OAI.UniversalTensorSquare.degreeTree62_291All`, `OAI.UniversalTensorSquare.degreeTree62_293All`, `OAI.UniversalTensorSquare.degreeTree62_302All`, `OAI.UniversalTensorSquare.degreeTree62_307All`, `OAI.UniversalTensorSquare.degreeTree62_309All`, `OAI.UniversalTensorSquare.degreeTree62_310All`, `OAI.UniversalTensorSquare.degreeTree62_39All`, `OAI.UniversalTensorSquare.degreeTree62_680All`, `OAI.UniversalTensorSquare.degreeTree62_713All`, `OAI.UniversalTensorSquare.degreeTree62_722All`, `OAI.UniversalTensorSquare.degreeTree62_73All`, `OAI.UniversalTensorSquare.degreeTree62_89All`, `OAI.UniversalTensorSquare.degreeTree62_8All`, `OAI.UniversalTensorSquare.sg32021`, `OAI.UniversalTensorSquare.sg32024`, `OAI.UniversalTensorSquare.sg32144`, `OAI.UniversalTensorSquare.sg32331`, `OAI.UniversalTensorSquare.sg32471`, `OAI.UniversalTensorSquare.sg32673`, `OAI.UniversalTensorSquare.sg32696`, `OAI.UniversalTensorSquare.sg32711`, `OAI.UniversalTensorSquare.sg32856`, `OAI.UniversalTensorSquare.sg33077`, `OAI.UniversalTensorSquare.sg33081`, `OAI.UniversalTensorSquare.sg33416`, `OAI.UniversalTensorSquare.sg33608`, `OAI.UniversalTensorSquare.sg33795`, `OAI.UniversalTensorSquare.sg34070`, `OAI.UniversalTensorSquare.sg34267`, `OAI.UniversalTensorSquare.sg34416`, `OAI.UniversalTensorSquare.sg37691`, `OAI.UniversalTensorSquare.sg37711`, `OAI.UniversalTensorSquare.sg37713`, `OAI.UniversalTensorSquare.sg38768`, `OAI.UniversalTensorSquare.sg38906` and `OAI.UniversalTensorSquare.sg38919` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean (declaration OAI.UniversalTensorSquare.sg20524)

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

lemma sg20524 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,3,2,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
