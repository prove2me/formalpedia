-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg543
-- name    : OAI.UniversalTensorSquare.sg543
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T22:43:50.785174+00:00
-- url     : https://prove2.me/theorems/bd2b81ee-c727-44fb-a4d6-b5cf444ebf61
-- title:
--   OAI.UniversalTensorSquare.sg543: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg543` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg543 : RowSquare [4,2,1,1,1] [3,3,3]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_248All`, `OAI.UniversalTensorSquare.sg24791`, `OAI.UniversalTensorSquare.sg25113`, `OAI.UniversalTensorSquare.sg25150`, `OAI.UniversalTensorSquare.sg27580`, `OAI.UniversalTensorSquare.sg30482`, `OAI.UniversalTensorSquare.sg30488`, `OAI.UniversalTensorSquare.sg30496`, `OAI.UniversalTensorSquare.sg34626`, `OAI.UniversalTensorSquare.sg34648`, `OAI.UniversalTensorSquare.sg37121`, `OAI.UniversalTensorSquare.sg38442`, `OAI.UniversalTensorSquare.sg4789`, `OAI.UniversalTensorSquare.sg6315`, `OAI.UniversalTensorSquare.sg8666`, `OAI.UniversalTensorSquare.sg9319` and `OAI.UniversalTensorSquare.sg9320` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean (declaration OAI.UniversalTensorSquare.sg543)

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

lemma sg543 : RowSquare [4,2,1,1,1] [3,3,3] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
