-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg779
-- name    : OAI.UniversalTensorSquare.sg779
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:39:43.511194+00:00
-- url     : https://prove2.me/theorems/985efab6-28db-44e0-b52a-aa0bc0dd78e4
-- title:
--   OAI.UniversalTensorSquare.sg779: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg779` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg779 : RowSquare [3,3,1,1,1,1] [5,4,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree24_11All`, `OAI.UniversalTensorSquare.degreeTree24_12All`, `OAI.UniversalTensorSquare.degreeTree26_26All`, `OAI.UniversalTensorSquare.degreeTree26_27All`, `OAI.UniversalTensorSquare.degreeTree26_42All`, `OAI.UniversalTensorSquare.degreeTree26_5All`, `OAI.UniversalTensorSquare.degreeTree26_6All`, `OAI.UniversalTensorSquare.sg12058`, `OAI.UniversalTensorSquare.sg12059`, `OAI.UniversalTensorSquare.sg12060`, `OAI.UniversalTensorSquare.sg12993`, `OAI.UniversalTensorSquare.sg12994`, `OAI.UniversalTensorSquare.sg12995`, `OAI.UniversalTensorSquare.sg12996`, `OAI.UniversalTensorSquare.sg13015`, `OAI.UniversalTensorSquare.sg13016`, `OAI.UniversalTensorSquare.sg13017`, `OAI.UniversalTensorSquare.sg13018`, `OAI.UniversalTensorSquare.sg13217`, `OAI.UniversalTensorSquare.sg13218` and `OAI.UniversalTensorSquare.sg13363` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes1.lean (declaration OAI.UniversalTensorSquare.sg779)

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

lemma sg779 : RowSquare [3,3,1,1,1,1] [5,4,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
