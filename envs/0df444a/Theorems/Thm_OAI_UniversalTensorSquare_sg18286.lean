-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg18286
-- name    : OAI.UniversalTensorSquare.sg18286
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:39:24.458807+00:00
-- url     : https://prove2.me/theorems/09754328-9e43-4b7d-a1e4-82b0db70d153
-- title:
--   OAI.UniversalTensorSquare.sg18286: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg18286` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes44.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes44.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg18286 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [4,4,3,3,3,3,3,3,2,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_205All`, `OAI.UniversalTensorSquare.degreeTree62_227All`, `OAI.UniversalTensorSquare.degreeTree62_337All`, `OAI.UniversalTensorSquare.degreeTree62_397All`, `OAI.UniversalTensorSquare.degreeTree62_402All`, `OAI.UniversalTensorSquare.sg32189`, `OAI.UniversalTensorSquare.sg32198`, `OAI.UniversalTensorSquare.sg32244`, `OAI.UniversalTensorSquare.sg32923`, `OAI.UniversalTensorSquare.sg33064`, `OAI.UniversalTensorSquare.sg33650`, `OAI.UniversalTensorSquare.sg33659`, `OAI.UniversalTensorSquare.sg33904`, `OAI.UniversalTensorSquare.sg33940`, `OAI.UniversalTensorSquare.sg33975`, `OAI.UniversalTensorSquare.sg34254`, `OAI.UniversalTensorSquare.sg35813`, `OAI.UniversalTensorSquare.sg36537`, `OAI.UniversalTensorSquare.sg36592`, `OAI.UniversalTensorSquare.sg36697` and `OAI.UniversalTensorSquare.sg36775` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes44.lean (declaration OAI.UniversalTensorSquare.sg18286)

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

lemma sg18286 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [4,4,3,3,3,3,3,3,2,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
