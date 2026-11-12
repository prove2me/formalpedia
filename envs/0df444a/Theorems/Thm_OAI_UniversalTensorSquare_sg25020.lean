-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg25020
-- name    : OAI.UniversalTensorSquare.sg25020
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T03:03:03.811914+00:00
-- url     : https://prove2.me/theorems/ee8f4c72-3064-4e56-9caa-c025e87a51c0
-- title:
--   OAI.UniversalTensorSquare.sg25020: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg25020` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes61.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes61.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg25020 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,2,2,1,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.degreeTree43_105All` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes61.lean (declaration OAI.UniversalTensorSquare.sg25020)

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

lemma sg25020 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,2,2,1,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
