-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg2406
-- name    : OAI.UniversalTensorSquare.sg2406
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T01:42:26.53542+00:00
-- url     : https://prove2.me/theorems/155406fc-4702-4773-bd19-3fed3758d0c2
-- title:
--   OAI.UniversalTensorSquare.sg2406: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg2406` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg2406 : RowSquare [8,3,1,1] [3,3,3,2,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_114All`, `OAI.UniversalTensorSquare.degreeTree62_193All`, `OAI.UniversalTensorSquare.degreeTree62_195All`, `OAI.UniversalTensorSquare.degreeTree62_209All`, `OAI.UniversalTensorSquare.degreeTree62_210All`, `OAI.UniversalTensorSquare.degreeTree62_255All`, `OAI.UniversalTensorSquare.degreeTree62_267All`, `OAI.UniversalTensorSquare.degreeTree62_270All`, `OAI.UniversalTensorSquare.degreeTree62_271All`, `OAI.UniversalTensorSquare.degreeTree62_273All`, `OAI.UniversalTensorSquare.degreeTree62_283All`, `OAI.UniversalTensorSquare.degreeTree62_287All`, `OAI.UniversalTensorSquare.degreeTree62_288All`, `OAI.UniversalTensorSquare.degreeTree62_290All`, `OAI.UniversalTensorSquare.degreeTree62_291All`, `OAI.UniversalTensorSquare.degreeTree62_297All`, `OAI.UniversalTensorSquare.degreeTree62_307All`, `OAI.UniversalTensorSquare.degreeTree62_470All`, `OAI.UniversalTensorSquare.degreeTree62_485All`, `OAI.UniversalTensorSquare.degreeTree62_510All`, `OAI.UniversalTensorSquare.degreeTree62_692All`, `OAI.UniversalTensorSquare.degreeTree62_694All`, `OAI.UniversalTensorSquare.sg19116`, `OAI.UniversalTensorSquare.sg33282`, `OAI.UniversalTensorSquare.sg33289`, `OAI.UniversalTensorSquare.sg34695`, `OAI.UniversalTensorSquare.sg35041`, `OAI.UniversalTensorSquare.sg35043`, `OAI.UniversalTensorSquare.sg35045`, `OAI.UniversalTensorSquare.sg35047`, `OAI.UniversalTensorSquare.sg35195`, `OAI.UniversalTensorSquare.sg35204`, `OAI.UniversalTensorSquare.sg35335`, `OAI.UniversalTensorSquare.sg37400`, `OAI.UniversalTensorSquare.sg37402`, `OAI.UniversalTensorSquare.sg38130`, `OAI.UniversalTensorSquare.sg38132`, `OAI.UniversalTensorSquare.sg38495`, `OAI.UniversalTensorSquare.sg38538`, `OAI.UniversalTensorSquare.sg38550`, `OAI.UniversalTensorSquare.sg38639`, `OAI.UniversalTensorSquare.sg38686`, `OAI.UniversalTensorSquare.sg39321`, `OAI.UniversalTensorSquare.sg39582`, `OAI.UniversalTensorSquare.sg41352`, `OAI.UniversalTensorSquare.sg41987`, `OAI.UniversalTensorSquare.sg42432`, `OAI.UniversalTensorSquare.sg42483` and `OAI.UniversalTensorSquare.sg42484` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean (declaration OAI.UniversalTensorSquare.sg2406)

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

lemma sg2406 : RowSquare [8,3,1,1] [3,3,3,2,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
