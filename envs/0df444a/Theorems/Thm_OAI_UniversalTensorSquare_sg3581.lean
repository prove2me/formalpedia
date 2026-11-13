-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg3581
-- name    : OAI.UniversalTensorSquare.sg3581
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T15:39:23.551183+00:00
-- url     : https://prove2.me/theorems/c11083e6-5b56-4e72-b829-f1f6ca816ad7
-- title:
--   OAI.UniversalTensorSquare.sg3581: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg3581` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg3581 : RowSquare [8,3,1,1,1,1] [4,3,2,2,2,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_344All`, `OAI.UniversalTensorSquare.degreeTree62_348All`, `OAI.UniversalTensorSquare.sg35832`, `OAI.UniversalTensorSquare.sg36547`, `OAI.UniversalTensorSquare.sg36557`, `OAI.UniversalTensorSquare.sg36559`, `OAI.UniversalTensorSquare.sg36561`, `OAI.UniversalTensorSquare.sg37030`, `OAI.UniversalTensorSquare.sg41729`, `OAI.UniversalTensorSquare.sg41824` and `OAI.UniversalTensorSquare.sg42915` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean (declaration OAI.UniversalTensorSquare.sg3581)

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

lemma sg3581 : RowSquare [8,3,1,1,1,1] [4,3,2,2,2,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
