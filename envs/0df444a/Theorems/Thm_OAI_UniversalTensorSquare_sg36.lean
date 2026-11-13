-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg36
-- name    : OAI.UniversalTensorSquare.sg36
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T15:46:31.87336+00:00
-- url     : https://prove2.me/theorems/edc95483-873d-49d5-86d0-dc080f7e56b6
-- title:
--   OAI.UniversalTensorSquare.sg36: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg36` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg36 : RowSquare [3,1,1] [3,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg1169`, `OAI.UniversalTensorSquare.sg1639`, `OAI.UniversalTensorSquare.sg17457`, `OAI.UniversalTensorSquare.sg18291`, `OAI.UniversalTensorSquare.sg18364`, `OAI.UniversalTensorSquare.sg2585`, `OAI.UniversalTensorSquare.sg2912`, `OAI.UniversalTensorSquare.sg32051`, `OAI.UniversalTensorSquare.sg32054`, `OAI.UniversalTensorSquare.sg32734`, `OAI.UniversalTensorSquare.sg32747`, `OAI.UniversalTensorSquare.sg32750`, `OAI.UniversalTensorSquare.sg32869`, `OAI.UniversalTensorSquare.sg34639`, `OAI.UniversalTensorSquare.sg35289`, `OAI.UniversalTensorSquare.sg35616`, `OAI.UniversalTensorSquare.sg35619`, `OAI.UniversalTensorSquare.sg35621`, `OAI.UniversalTensorSquare.sg35818`, `OAI.UniversalTensorSquare.sg35837`, `OAI.UniversalTensorSquare.sg35848`, `OAI.UniversalTensorSquare.sg35850`, `OAI.UniversalTensorSquare.sg35852`, `OAI.UniversalTensorSquare.sg35868`, `OAI.UniversalTensorSquare.sg35872`, `OAI.UniversalTensorSquare.sg35874`, `OAI.UniversalTensorSquare.sg35876`, `OAI.UniversalTensorSquare.sg37067`, `OAI.UniversalTensorSquare.sg37900`, `OAI.UniversalTensorSquare.sg39118`, `OAI.UniversalTensorSquare.sg4860`, `OAI.UniversalTensorSquare.sg503`, `OAI.UniversalTensorSquare.sg703`, `OAI.UniversalTensorSquare.sg771` and `OAI.UniversalTensorSquare.sg779` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg36)

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

lemma sg36 : RowSquare [3,1,1] [3,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
