-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg2724
-- name    : OAI.UniversalTensorSquare.sg2724
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T09:17:27.422504+00:00
-- url     : https://prove2.me/theorems/5f49d1c1-0ce0-4dde-8438-9e4a6cd60baf
-- title:
--   OAI.UniversalTensorSquare.sg2724: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg2724` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg2724 : RowSquare [7,3,1,1,1,1] [3,3,3,3,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg14328`, `OAI.UniversalTensorSquare.sg34172`, `OAI.UniversalTensorSquare.sg34362`, `OAI.UniversalTensorSquare.sg34366`, `OAI.UniversalTensorSquare.sg34393`, `OAI.UniversalTensorSquare.sg35357`, `OAI.UniversalTensorSquare.sg35367`, `OAI.UniversalTensorSquare.sg37430`, `OAI.UniversalTensorSquare.sg37634`, `OAI.UniversalTensorSquare.sg38721`, `OAI.UniversalTensorSquare.sg38873`, `OAI.UniversalTensorSquare.sg39936`, `OAI.UniversalTensorSquare.sg39954`, `OAI.UniversalTensorSquare.sg41824` and `OAI.UniversalTensorSquare.sg42349` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes5.lean (declaration OAI.UniversalTensorSquare.sg2724)

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

lemma sg2724 : RowSquare [7,3,1,1,1,1] [3,3,3,3,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
