-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg4926
-- name    : OAI.UniversalTensorSquare.sg4926
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:18:13.581925+00:00
-- url     : https://prove2.me/theorems/a7aea798-bd8b-4b3c-987f-f63ea8e4605d
-- title:
--   OAI.UniversalTensorSquare.sg4926: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg4926` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes11.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes11.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg4926 : RowSquare [8,4,3,2] [3,2,2,2,2,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_313All`, `OAI.UniversalTensorSquare.degreeTree62_318All`, `OAI.UniversalTensorSquare.degreeTree62_394All`, `OAI.UniversalTensorSquare.degreeTree62_518All`, `OAI.UniversalTensorSquare.degreeTree62_861All`, `OAI.UniversalTensorSquare.sg35680`, `OAI.UniversalTensorSquare.sg35714`, `OAI.UniversalTensorSquare.sg35900`, `OAI.UniversalTensorSquare.sg36410`, `OAI.UniversalTensorSquare.sg40375`, `OAI.UniversalTensorSquare.sg40401` and `OAI.UniversalTensorSquare.sg40787` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes11.lean (declaration OAI.UniversalTensorSquare.sg4926)

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

lemma sg4926 : RowSquare [8,4,3,2] [3,2,2,2,2,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
