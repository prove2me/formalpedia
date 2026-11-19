-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg834
-- name    : OAI.UniversalTensorSquare.sg834
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T23:35:49.937014+00:00
-- url     : https://prove2.me/theorems/c5b79fcf-1e77-4cdd-8b03-98381f222cc8
-- title:
--   OAI.UniversalTensorSquare.sg834: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg834` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg834 : RowSquare [4,2,2,2] [2,2,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_943All`, `OAI.UniversalTensorSquare.sg14816`, `OAI.UniversalTensorSquare.sg15710`, `OAI.UniversalTensorSquare.sg15756`, `OAI.UniversalTensorSquare.sg16376`, `OAI.UniversalTensorSquare.sg16778`, `OAI.UniversalTensorSquare.sg16786`, `OAI.UniversalTensorSquare.sg31959`, `OAI.UniversalTensorSquare.sg31989`, `OAI.UniversalTensorSquare.sg31993`, `OAI.UniversalTensorSquare.sg32766`, `OAI.UniversalTensorSquare.sg32901`, `OAI.UniversalTensorSquare.sg33643`, `OAI.UniversalTensorSquare.sg3420`, `OAI.UniversalTensorSquare.sg34904`, `OAI.UniversalTensorSquare.sg37643`, `OAI.UniversalTensorSquare.sg37644`, `OAI.UniversalTensorSquare.sg37673`, `OAI.UniversalTensorSquare.sg37674`, `OAI.UniversalTensorSquare.sg38879`, `OAI.UniversalTensorSquare.sg38898`, `OAI.UniversalTensorSquare.sg42474`, `OAI.UniversalTensorSquare.sg4329`, `OAI.UniversalTensorSquare.sg6004` and `OAI.UniversalTensorSquare.sg8013` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean (declaration OAI.UniversalTensorSquare.sg834)

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

lemma sg834 : RowSquare [4,2,2,2] [2,2,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
