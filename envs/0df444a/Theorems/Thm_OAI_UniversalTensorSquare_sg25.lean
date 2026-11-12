-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg25
-- name    : OAI.UniversalTensorSquare.sg25
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T03:01:41.537195+00:00
-- url     : https://prove2.me/theorems/90c0e45a-a02c-468a-b24c-d22731f11c08
-- title:
--   OAI.UniversalTensorSquare.sg25: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg25` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg25 : RowSquare [2,1,1,1] [5]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_305All`, `OAI.UniversalTensorSquare.sg21420`, `OAI.UniversalTensorSquare.sg21421`, `OAI.UniversalTensorSquare.sg22418`, `OAI.UniversalTensorSquare.sg22419`, `OAI.UniversalTensorSquare.sg22420`, `OAI.UniversalTensorSquare.sg22421`, `OAI.UniversalTensorSquare.sg27605`, `OAI.UniversalTensorSquare.sg27606`, `OAI.UniversalTensorSquare.sg27609`, `OAI.UniversalTensorSquare.sg27610` and `OAI.UniversalTensorSquare.sg4058` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg25)

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

lemma sg25 : RowSquare [2,1,1,1] [5] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
