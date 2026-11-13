-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg9195
-- name    : OAI.UniversalTensorSquare.sg9195
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:51:57.722464+00:00
-- url     : https://prove2.me/theorems/6ec5c576-7083-4622-a54d-5e43c25c6e6f
-- title:
--   OAI.UniversalTensorSquare.sg9195: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg9195` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes21.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes21.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg9195 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,2,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_148All`, `OAI.UniversalTensorSquare.degreeTree43_171All`, `OAI.UniversalTensorSquare.degreeTree43_425All`, `OAI.UniversalTensorSquare.degreeTree43_52All`, `OAI.UniversalTensorSquare.degreeTree43_57All`, `OAI.UniversalTensorSquare.sg25599`, `OAI.UniversalTensorSquare.sg25852`, `OAI.UniversalTensorSquare.sg26189`, `OAI.UniversalTensorSquare.sg26199` and `OAI.UniversalTensorSquare.sg26937` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes21.lean (declaration OAI.UniversalTensorSquare.sg9195)

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

lemma sg9195 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,2,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
