-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg9170
-- name    : OAI.UniversalTensorSquare.sg9170
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:51:55.563855+00:00
-- url     : https://prove2.me/theorems/ae91d7fd-d9c5-4f14-8fdb-6b31d1cf9376
-- title:
--   OAI.UniversalTensorSquare.sg9170: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg9170` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes21.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes21.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg9170 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_122All`, `OAI.UniversalTensorSquare.degreeTree43_125All`, `OAI.UniversalTensorSquare.degreeTree43_16All`, `OAI.UniversalTensorSquare.degreeTree43_46All`, `OAI.UniversalTensorSquare.sg24356`, `OAI.UniversalTensorSquare.sg24380`, `OAI.UniversalTensorSquare.sg24921` and `OAI.UniversalTensorSquare.sg25222` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes21.lean (declaration OAI.UniversalTensorSquare.sg9170)

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

lemma sg9170 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
