-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg199
-- name    : OAI.UniversalTensorSquare.sg199
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:49:17.904096+00:00
-- url     : https://prove2.me/theorems/6df6fd93-2e85-4f51-a02c-fe5465d1c572
-- title:
--   OAI.UniversalTensorSquare.sg199: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg199` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg199 : RowSquare [4,2,1] [3,3,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_13All`, `OAI.UniversalTensorSquare.degreeTree62_4All`, `OAI.UniversalTensorSquare.degreeTree62_659All`, `OAI.UniversalTensorSquare.degreeTree62_662All`, `OAI.UniversalTensorSquare.degreeTree62_980All`, `OAI.UniversalTensorSquare.sg17227`, `OAI.UniversalTensorSquare.sg17576`, `OAI.UniversalTensorSquare.sg26974`, `OAI.UniversalTensorSquare.sg26976`, `OAI.UniversalTensorSquare.sg26977`, `OAI.UniversalTensorSquare.sg26978`, `OAI.UniversalTensorSquare.sg26979`, `OAI.UniversalTensorSquare.sg32090`, `OAI.UniversalTensorSquare.sg33248`, `OAI.UniversalTensorSquare.sg33423`, `OAI.UniversalTensorSquare.sg33429`, `OAI.UniversalTensorSquare.sg33477`, `OAI.UniversalTensorSquare.sg38086`, `OAI.UniversalTensorSquare.sg39035`, `OAI.UniversalTensorSquare.sg40103`, `OAI.UniversalTensorSquare.sg40104` and `OAI.UniversalTensorSquare.sg40119` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean (declaration OAI.UniversalTensorSquare.sg199)

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

lemma sg199 : RowSquare [4,2,1] [3,3,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
