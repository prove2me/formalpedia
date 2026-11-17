-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg320
-- name    : OAI.UniversalTensorSquare.sg320
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T01:47:02.905449+00:00
-- url     : https://prove2.me/theorems/841ad1d4-3cff-4115-802d-215fe038a83a
-- title:
--   OAI.UniversalTensorSquare.sg320: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg320` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg320 : RowSquare [4,1,1,1,1] [3,3,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_234All`, `OAI.UniversalTensorSquare.sg22161`, `OAI.UniversalTensorSquare.sg22178`, `OAI.UniversalTensorSquare.sg23024`, `OAI.UniversalTensorSquare.sg24816`, `OAI.UniversalTensorSquare.sg24827`, `OAI.UniversalTensorSquare.sg24832`, `OAI.UniversalTensorSquare.sg24887`, `OAI.UniversalTensorSquare.sg26686`, `OAI.UniversalTensorSquare.sg27329`, `OAI.UniversalTensorSquare.sg27347`, `OAI.UniversalTensorSquare.sg27353`, `OAI.UniversalTensorSquare.sg27384`, `OAI.UniversalTensorSquare.sg27549`, `OAI.UniversalTensorSquare.sg30351`, `OAI.UniversalTensorSquare.sg30512`, `OAI.UniversalTensorSquare.sg30553`, `OAI.UniversalTensorSquare.sg31252`, `OAI.UniversalTensorSquare.sg31346`, `OAI.UniversalTensorSquare.sg31692`, `OAI.UniversalTensorSquare.sg31741`, `OAI.UniversalTensorSquare.sg31753` and `OAI.UniversalTensorSquare.sg596` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean (declaration OAI.UniversalTensorSquare.sg320)

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

lemma sg320 : RowSquare [4,1,1,1,1] [3,3,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
