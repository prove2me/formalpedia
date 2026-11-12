-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg10219
-- name    : OAI.UniversalTensorSquare.sg10219
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T20:25:07.165304+00:00
-- url     : https://prove2.me/theorems/6302110c-7727-49a5-8004-70b010c7f4fe
-- title:
--   OAI.UniversalTensorSquare.sg10219: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg10219` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes24.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes24.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg10219 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,4,3,3,2,2,2,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_15All`, `OAI.UniversalTensorSquare.degreeTree43_27All`, `OAI.UniversalTensorSquare.degreeTree43_33All`, `OAI.UniversalTensorSquare.degreeTree43_342All` and `OAI.UniversalTensorSquare.degreeTree43_37All` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes24.lean (declaration OAI.UniversalTensorSquare.sg10219)

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

lemma sg10219 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [5,4,3,3,2,2,2,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
