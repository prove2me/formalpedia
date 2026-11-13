-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg3633
-- name    : OAI.UniversalTensorSquare.sg3633
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T15:59:10.864939+00:00
-- url     : https://prove2.me/theorems/6a3d2ea8-fe7d-4dad-b5d0-f6a041b9db56
-- title:
--   OAI.UniversalTensorSquare.sg3633: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg3633` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg3633 : RowSquare [8,3,2,2] [3,2,2,2,2,2,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_364All`, `OAI.UniversalTensorSquare.degreeTree62_413All`, `OAI.UniversalTensorSquare.degreeTree62_465All`, `OAI.UniversalTensorSquare.sg15886`, `OAI.UniversalTensorSquare.sg35523`, `OAI.UniversalTensorSquare.sg35527`, `OAI.UniversalTensorSquare.sg35529`, `OAI.UniversalTensorSquare.sg35610`, `OAI.UniversalTensorSquare.sg35686`, `OAI.UniversalTensorSquare.sg35690`, `OAI.UniversalTensorSquare.sg35692`, `OAI.UniversalTensorSquare.sg35786`, `OAI.UniversalTensorSquare.sg35869`, `OAI.UniversalTensorSquare.sg35933`, `OAI.UniversalTensorSquare.sg36171`, `OAI.UniversalTensorSquare.sg36210`, `OAI.UniversalTensorSquare.sg36443`, `OAI.UniversalTensorSquare.sg36752`, `OAI.UniversalTensorSquare.sg36789`, `OAI.UniversalTensorSquare.sg36896`, `OAI.UniversalTensorSquare.sg37206`, `OAI.UniversalTensorSquare.sg37336`, `OAI.UniversalTensorSquare.sg40254`, `OAI.UniversalTensorSquare.sg40257`, `OAI.UniversalTensorSquare.sg40258`, `OAI.UniversalTensorSquare.sg40313`, `OAI.UniversalTensorSquare.sg40357`, `OAI.UniversalTensorSquare.sg40422`, `OAI.UniversalTensorSquare.sg40493`, `OAI.UniversalTensorSquare.sg40599`, `OAI.UniversalTensorSquare.sg40682`, `OAI.UniversalTensorSquare.sg40808`, `OAI.UniversalTensorSquare.sg40895`, `OAI.UniversalTensorSquare.sg40914`, `OAI.UniversalTensorSquare.sg40986`, `OAI.UniversalTensorSquare.sg41022`, `OAI.UniversalTensorSquare.sg41094`, `OAI.UniversalTensorSquare.sg41225`, `OAI.UniversalTensorSquare.sg41257`, `OAI.UniversalTensorSquare.sg41572`, `OAI.UniversalTensorSquare.sg41600`, `OAI.UniversalTensorSquare.sg41680`, `OAI.UniversalTensorSquare.sg41706` and `OAI.UniversalTensorSquare.sg41868` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean (declaration OAI.UniversalTensorSquare.sg3633)

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

lemma sg3633 : RowSquare [8,3,2,2] [3,2,2,2,2,2,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
