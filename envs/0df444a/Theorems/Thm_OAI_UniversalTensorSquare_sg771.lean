-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg771
-- name    : OAI.UniversalTensorSquare.sg771
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:38:43.422203+00:00
-- url     : https://prove2.me/theorems/37518726-9145-406f-8fe5-a51d9ed7a1c2
-- title:
--   OAI.UniversalTensorSquare.sg771: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg771` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg771 : RowSquare [3,3,1,1,1,1] [4,3,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg12258`, `OAI.UniversalTensorSquare.sg13040`, `OAI.UniversalTensorSquare.sg13041`, `OAI.UniversalTensorSquare.sg13042`, `OAI.UniversalTensorSquare.sg13043`, `OAI.UniversalTensorSquare.sg13249`, `OAI.UniversalTensorSquare.sg13250`, `OAI.UniversalTensorSquare.sg13251`, `OAI.UniversalTensorSquare.sg13252`, `OAI.UniversalTensorSquare.sg13374`, `OAI.UniversalTensorSquare.sg13375`, `OAI.UniversalTensorSquare.sg13376`, `OAI.UniversalTensorSquare.sg13377`, `OAI.UniversalTensorSquare.sg13448`, `OAI.UniversalTensorSquare.sg13449`, `OAI.UniversalTensorSquare.sg13450` and `OAI.UniversalTensorSquare.sg7853` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes1.lean (declaration OAI.UniversalTensorSquare.sg771)

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

lemma sg771 : RowSquare [3,3,1,1,1,1] [4,3,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
