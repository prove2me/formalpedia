-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg20640
-- name    : OAI.UniversalTensorSquare.sg20640
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:54:25.420605+00:00
-- url     : https://prove2.me/theorems/8ea9f485-dfc6-4f48-9392-705a8466d692
-- title:
--   OAI.UniversalTensorSquare.sg20640: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg20640` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes50.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes50.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg20640 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [5,4,3,3,3,3,3,2,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_351All`, `OAI.UniversalTensorSquare.degreeTree62_445All`, `OAI.UniversalTensorSquare.degreeTree62_452All`, `OAI.UniversalTensorSquare.degreeTree62_475All`, `OAI.UniversalTensorSquare.degreeTree62_574All`, `OAI.UniversalTensorSquare.degreeTree62_577All`, `OAI.UniversalTensorSquare.degreeTree62_615All`, `OAI.UniversalTensorSquare.degreeTree62_621All`, `OAI.UniversalTensorSquare.degreeTree62_625All`, `OAI.UniversalTensorSquare.degreeTree62_678All`, `OAI.UniversalTensorSquare.degreeTree62_679All`, `OAI.UniversalTensorSquare.degreeTree62_722All`, `OAI.UniversalTensorSquare.degreeTree62_91All`, `OAI.UniversalTensorSquare.sg32866`, `OAI.UniversalTensorSquare.sg32987`, `OAI.UniversalTensorSquare.sg32996`, `OAI.UniversalTensorSquare.sg33036`, `OAI.UniversalTensorSquare.sg33069`, `OAI.UniversalTensorSquare.sg36618`, `OAI.UniversalTensorSquare.sg36998`, `OAI.UniversalTensorSquare.sg37051`, `OAI.UniversalTensorSquare.sg37066`, `OAI.UniversalTensorSquare.sg37961`, `OAI.UniversalTensorSquare.sg37975`, `OAI.UniversalTensorSquare.sg38285`, `OAI.UniversalTensorSquare.sg38323`, `OAI.UniversalTensorSquare.sg38331`, `OAI.UniversalTensorSquare.sg38368`, `OAI.UniversalTensorSquare.sg38853`, `OAI.UniversalTensorSquare.sg38858`, `OAI.UniversalTensorSquare.sg38881`, `OAI.UniversalTensorSquare.sg39123`, `OAI.UniversalTensorSquare.sg39170`, `OAI.UniversalTensorSquare.sg39178`, `OAI.UniversalTensorSquare.sg39470`, `OAI.UniversalTensorSquare.sg39498`, `OAI.UniversalTensorSquare.sg39503`, `OAI.UniversalTensorSquare.sg39527`, `OAI.UniversalTensorSquare.sg39924`, `OAI.UniversalTensorSquare.sg39941`, `OAI.UniversalTensorSquare.sg39961`, `OAI.UniversalTensorSquare.sg39974` and `OAI.UniversalTensorSquare.sg40521` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes50.lean (declaration OAI.UniversalTensorSquare.sg20640)

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

lemma sg20640 : RowSquare [9,8,2,2,2,1,1,1,1,1,1,1,1] [5,4,3,3,3,3,3,2,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
