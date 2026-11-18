-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg348
-- name    : OAI.UniversalTensorSquare.sg348
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:17:59.341939+00:00
-- url     : https://prove2.me/theorems/79d65fca-64f8-405c-8d5d-a15201a3b49d
-- title:
--   OAI.UniversalTensorSquare.sg348: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg348` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg348 : RowSquare [4,2,2] [2,2,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree24_17All`, `OAI.UniversalTensorSquare.degreeTree26_32All`, `OAI.UniversalTensorSquare.degreeTree62_209All`, `OAI.UniversalTensorSquare.degreeTree62_213All`, `OAI.UniversalTensorSquare.degreeTree62_677All`, `OAI.UniversalTensorSquare.degreeTree62_986All`, `OAI.UniversalTensorSquare.sg16237`, `OAI.UniversalTensorSquare.sg16440`, `OAI.UniversalTensorSquare.sg16565`, `OAI.UniversalTensorSquare.sg33003`, `OAI.UniversalTensorSquare.sg33005`, `OAI.UniversalTensorSquare.sg34540`, `OAI.UniversalTensorSquare.sg34562`, `OAI.UniversalTensorSquare.sg36702`, `OAI.UniversalTensorSquare.sg37870`, `OAI.UniversalTensorSquare.sg37889`, `OAI.UniversalTensorSquare.sg37894`, `OAI.UniversalTensorSquare.sg37896`, `OAI.UniversalTensorSquare.sg37898`, `OAI.UniversalTensorSquare.sg37964`, `OAI.UniversalTensorSquare.sg37976`, `OAI.UniversalTensorSquare.sg38070`, `OAI.UniversalTensorSquare.sg38333`, `OAI.UniversalTensorSquare.sg38715`, `OAI.UniversalTensorSquare.sg38837`, `OAI.UniversalTensorSquare.sg38886`, `OAI.UniversalTensorSquare.sg39161`, `OAI.UniversalTensorSquare.sg39280`, `OAI.UniversalTensorSquare.sg39329`, `OAI.UniversalTensorSquare.sg39454`, `OAI.UniversalTensorSquare.sg39484`, `OAI.UniversalTensorSquare.sg39506`, `OAI.UniversalTensorSquare.sg39507`, `OAI.UniversalTensorSquare.sg39726`, `OAI.UniversalTensorSquare.sg39810`, `OAI.UniversalTensorSquare.sg39830`, `OAI.UniversalTensorSquare.sg39942`, `OAI.UniversalTensorSquare.sg40866`, `OAI.UniversalTensorSquare.sg40893`, `OAI.UniversalTensorSquare.sg41953`, `OAI.UniversalTensorSquare.sg42001`, `OAI.UniversalTensorSquare.sg42112`, `OAI.UniversalTensorSquare.sg42128`, `OAI.UniversalTensorSquare.sg42302`, `OAI.UniversalTensorSquare.sg42305`, `OAI.UniversalTensorSquare.sg42354`, `OAI.UniversalTensorSquare.sg42411`, `OAI.UniversalTensorSquare.sg42537`, `OAI.UniversalTensorSquare.sg42776`, `OAI.UniversalTensorSquare.sg42792`, `OAI.UniversalTensorSquare.sg42923` and `OAI.UniversalTensorSquare.sg7901` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean (declaration OAI.UniversalTensorSquare.sg348)

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

lemma sg348 : RowSquare [4,2,2] [2,2,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
