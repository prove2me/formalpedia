-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg503
-- name    : OAI.UniversalTensorSquare.sg503
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:19:14.099535+00:00
-- url     : https://prove2.me/theorems/ea7aab76-0d0f-4a99-a4bb-6f13f50743fc
-- title:
--   OAI.UniversalTensorSquare.sg503: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg503` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg503 : RowSquare [3,3,1,1,1] [5,4]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree22_12All`, `OAI.UniversalTensorSquare.degreeTree22_6All`, `OAI.UniversalTensorSquare.degreeTree22_8All`, `OAI.UniversalTensorSquare.degreeTree24_11All`, `OAI.UniversalTensorSquare.degreeTree24_19All`, `OAI.UniversalTensorSquare.degreeTree24_1All`, `OAI.UniversalTensorSquare.degreeTree24_3All`, `OAI.UniversalTensorSquare.degreeTree26_44All`, `OAI.UniversalTensorSquare.degreeTree26_53All`, `OAI.UniversalTensorSquare.degreeTree26_6All`, `OAI.UniversalTensorSquare.degree_pos24`, `OAI.UniversalTensorSquare.sg10924`, `OAI.UniversalTensorSquare.sg10930`, `OAI.UniversalTensorSquare.sg10942`, `OAI.UniversalTensorSquare.sg10992`, `OAI.UniversalTensorSquare.sg10999`, `OAI.UniversalTensorSquare.sg11892`, `OAI.UniversalTensorSquare.sg11893`, `OAI.UniversalTensorSquare.sg11894`, `OAI.UniversalTensorSquare.sg11912`, `OAI.UniversalTensorSquare.sg11913`, `OAI.UniversalTensorSquare.sg11914`, `OAI.UniversalTensorSquare.sg11936`, `OAI.UniversalTensorSquare.sg11966`, `OAI.UniversalTensorSquare.sg12014`, `OAI.UniversalTensorSquare.sg12065`, `OAI.UniversalTensorSquare.sg12066`, `OAI.UniversalTensorSquare.sg12067`, `OAI.UniversalTensorSquare.sg12096`, `OAI.UniversalTensorSquare.sg12126`, `OAI.UniversalTensorSquare.sg12222`, `OAI.UniversalTensorSquare.sg12282`, `OAI.UniversalTensorSquare.sg13047`, `OAI.UniversalTensorSquare.sg13057`, `OAI.UniversalTensorSquare.sg13081`, `OAI.UniversalTensorSquare.sg13092`, `OAI.UniversalTensorSquare.sg13136`, `OAI.UniversalTensorSquare.sg13242`, `OAI.UniversalTensorSquare.sg13243`, `OAI.UniversalTensorSquare.sg13244`, `OAI.UniversalTensorSquare.sg13245`, `OAI.UniversalTensorSquare.sg13256`, `OAI.UniversalTensorSquare.sg13266`, `OAI.UniversalTensorSquare.sg13289`, `OAI.UniversalTensorSquare.sg13381`, `OAI.UniversalTensorSquare.sg13395`, `OAI.UniversalTensorSquare.sg13412`, `OAI.UniversalTensorSquare.sg7871` and `OAI.UniversalTensorSquare.sg7938` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean (declaration OAI.UniversalTensorSquare.sg503)

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

lemma sg503 : RowSquare [3,3,1,1,1] [5,4] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
