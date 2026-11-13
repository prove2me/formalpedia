-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg9730
-- name    : OAI.UniversalTensorSquare.sg9730
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:58:32.984408+00:00
-- url     : https://prove2.me/theorems/b220da2d-4e08-4a1d-ba07-8383da8c27d9
-- title:
--   OAI.UniversalTensorSquare.sg9730: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg9730` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes22.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes22.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg9730 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_268All`, `OAI.UniversalTensorSquare.degreeTree43_269All`, `OAI.UniversalTensorSquare.degreeTree43_278All`, `OAI.UniversalTensorSquare.sg24002`, `OAI.UniversalTensorSquare.sg24504`, `OAI.UniversalTensorSquare.sg27208`, `OAI.UniversalTensorSquare.sg27239`, `OAI.UniversalTensorSquare.sg27351`, `OAI.UniversalTensorSquare.sg27428` and `OAI.UniversalTensorSquare.sg31202` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes22.lean (declaration OAI.UniversalTensorSquare.sg9730)

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

lemma sg9730 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
