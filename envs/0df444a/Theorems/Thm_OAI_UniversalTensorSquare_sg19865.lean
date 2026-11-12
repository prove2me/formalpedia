-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg19865
-- name    : OAI.UniversalTensorSquare.sg19865
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:48:45.575092+00:00
-- url     : https://prove2.me/theorems/24a6ec55-7e74-4a8c-af45-7c602a46851e
-- title:
--   OAI.UniversalTensorSquare.sg19865: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg19865` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes48.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes48.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg19865 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,5,4,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_450All`, `OAI.UniversalTensorSquare.degreeTree62_475All` and `OAI.UniversalTensorSquare.sg36963` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes48.lean (declaration OAI.UniversalTensorSquare.sg19865)

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

lemma sg19865 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,5,4,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
