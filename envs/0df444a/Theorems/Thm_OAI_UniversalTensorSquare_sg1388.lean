-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg1388
-- name    : OAI.UniversalTensorSquare.sg1388
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:16:25.83396+00:00
-- url     : https://prove2.me/theorems/b4da4cca-9f42-4ab5-b179-2a1a2dddac11
-- title:
--   OAI.UniversalTensorSquare.sg1388: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg1388` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg1388 : RowSquare [6,2,1,1,1] [4,4,2,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_321All`, `OAI.UniversalTensorSquare.degreeTree43_448All`, `OAI.UniversalTensorSquare.degreeTree43_646All`, `OAI.UniversalTensorSquare.sg26240`, `OAI.UniversalTensorSquare.sg26357`, `OAI.UniversalTensorSquare.sg26412`, `OAI.UniversalTensorSquare.sg26441`, `OAI.UniversalTensorSquare.sg26443`, `OAI.UniversalTensorSquare.sg27209`, `OAI.UniversalTensorSquare.sg27437`, `OAI.UniversalTensorSquare.sg27438`, `OAI.UniversalTensorSquare.sg30198`, `OAI.UniversalTensorSquare.sg30200`, `OAI.UniversalTensorSquare.sg30922`, `OAI.UniversalTensorSquare.sg31377`, `OAI.UniversalTensorSquare.sg7080`, `OAI.UniversalTensorSquare.sg9732` and `OAI.UniversalTensorSquare.sg9857` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean (declaration OAI.UniversalTensorSquare.sg1388)

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

lemma sg1388 : RowSquare [6,2,1,1,1] [4,4,2,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
