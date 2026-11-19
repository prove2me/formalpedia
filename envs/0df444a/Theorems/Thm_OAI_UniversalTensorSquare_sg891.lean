-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg891
-- name    : OAI.UniversalTensorSquare.sg891
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T23:56:03.822209+00:00
-- url     : https://prove2.me/theorems/1e3d9cfa-22ce-46eb-a158-7c9710d249a4
-- title:
--   OAI.UniversalTensorSquare.sg891: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg891` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg891 : RowSquare [5,1,1,1,1,1] [2,2,2,2,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_257All`, `OAI.UniversalTensorSquare.degreeTree62_34All`, `OAI.UniversalTensorSquare.sg10098`, `OAI.UniversalTensorSquare.sg10492`, `OAI.UniversalTensorSquare.sg1336`, `OAI.UniversalTensorSquare.sg16677`, `OAI.UniversalTensorSquare.sg25354`, `OAI.UniversalTensorSquare.sg26498`, `OAI.UniversalTensorSquare.sg26769`, `OAI.UniversalTensorSquare.sg26911`, `OAI.UniversalTensorSquare.sg26946`, `OAI.UniversalTensorSquare.sg26959`, `OAI.UniversalTensorSquare.sg32788`, `OAI.UniversalTensorSquare.sg34132`, `OAI.UniversalTensorSquare.sg34140`, `OAI.UniversalTensorSquare.sg34336`, `OAI.UniversalTensorSquare.sg34340`, `OAI.UniversalTensorSquare.sg35343`, `OAI.UniversalTensorSquare.sg35448`, `OAI.UniversalTensorSquare.sg36170`, `OAI.UniversalTensorSquare.sg36175`, `OAI.UniversalTensorSquare.sg36177`, `OAI.UniversalTensorSquare.sg36179`, `OAI.UniversalTensorSquare.sg36751`, `OAI.UniversalTensorSquare.sg36756`, `OAI.UniversalTensorSquare.sg36758`, `OAI.UniversalTensorSquare.sg36760`, `OAI.UniversalTensorSquare.sg37597`, `OAI.UniversalTensorSquare.sg38849`, `OAI.UniversalTensorSquare.sg39919`, `OAI.UniversalTensorSquare.sg4026`, `OAI.UniversalTensorSquare.sg4198`, `OAI.UniversalTensorSquare.sg42339`, `OAI.UniversalTensorSquare.sg4378`, `OAI.UniversalTensorSquare.sg4904`, `OAI.UniversalTensorSquare.sg6405`, `OAI.UniversalTensorSquare.sg8011` and `OAI.UniversalTensorSquare.sg9529` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean (declaration OAI.UniversalTensorSquare.sg891)

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

lemma sg891 : RowSquare [5,1,1,1,1,1] [2,2,2,2,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
