-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg8721
-- name    : OAI.UniversalTensorSquare.sg8721
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T23:47:04.011452+00:00
-- url     : https://prove2.me/theorems/69a63c1a-b57a-4da1-83be-31c3caaa05fd
-- title:
--   OAI.UniversalTensorSquare.sg8721: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg8721` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes20.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes20.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg8721 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_192All`, `OAI.UniversalTensorSquare.degreeTree43_47All`, `OAI.UniversalTensorSquare.degreeTree43_51All`, `OAI.UniversalTensorSquare.degreeTree43_75All`, `OAI.UniversalTensorSquare.sg23868`, `OAI.UniversalTensorSquare.sg23914`, `OAI.UniversalTensorSquare.sg24029`, `OAI.UniversalTensorSquare.sg24245`, `OAI.UniversalTensorSquare.sg24355`, `OAI.UniversalTensorSquare.sg24438`, `OAI.UniversalTensorSquare.sg24452`, `OAI.UniversalTensorSquare.sg24532`, `OAI.UniversalTensorSquare.sg24537`, `OAI.UniversalTensorSquare.sg24538`, `OAI.UniversalTensorSquare.sg24612`, `OAI.UniversalTensorSquare.sg24666`, `OAI.UniversalTensorSquare.sg24683`, `OAI.UniversalTensorSquare.sg24716`, `OAI.UniversalTensorSquare.sg24815`, `OAI.UniversalTensorSquare.sg24957`, `OAI.UniversalTensorSquare.sg25045`, `OAI.UniversalTensorSquare.sg25051`, `OAI.UniversalTensorSquare.sg25189`, `OAI.UniversalTensorSquare.sg25251`, `OAI.UniversalTensorSquare.sg25268`, `OAI.UniversalTensorSquare.sg25277`, `OAI.UniversalTensorSquare.sg25483`, `OAI.UniversalTensorSquare.sg25590`, `OAI.UniversalTensorSquare.sg25971`, `OAI.UniversalTensorSquare.sg26206`, `OAI.UniversalTensorSquare.sg26364`, `OAI.UniversalTensorSquare.sg26608`, `OAI.UniversalTensorSquare.sg26731`, `OAI.UniversalTensorSquare.sg26738`, `OAI.UniversalTensorSquare.sg26872`, `OAI.UniversalTensorSquare.sg26887`, `OAI.UniversalTensorSquare.sg26919`, `OAI.UniversalTensorSquare.sg26923`, `OAI.UniversalTensorSquare.sg26939`, `OAI.UniversalTensorSquare.sg26942`, `OAI.UniversalTensorSquare.sg26955`, `OAI.UniversalTensorSquare.sg27089`, `OAI.UniversalTensorSquare.sg27203`, `OAI.UniversalTensorSquare.sg27263`, `OAI.UniversalTensorSquare.sg27280`, `OAI.UniversalTensorSquare.sg27291`, `OAI.UniversalTensorSquare.sg27423`, `OAI.UniversalTensorSquare.sg27490`, `OAI.UniversalTensorSquare.sg28801`, `OAI.UniversalTensorSquare.sg28998`, `OAI.UniversalTensorSquare.sg29470`, `OAI.UniversalTensorSquare.sg29599`, `OAI.UniversalTensorSquare.sg29817`, `OAI.UniversalTensorSquare.sg29922`, `OAI.UniversalTensorSquare.sg29927`, `OAI.UniversalTensorSquare.sg29949`, `OAI.UniversalTensorSquare.sg29951`, `OAI.UniversalTensorSquare.sg30193`, `OAI.UniversalTensorSquare.sg30559`, `OAI.UniversalTensorSquare.sg30581`, `OAI.UniversalTensorSquare.sg30583`, `OAI.UniversalTensorSquare.sg30594`, `OAI.UniversalTensorSquare.sg30673`, `OAI.UniversalTensorSquare.sg30685`, `OAI.UniversalTensorSquare.sg30687`, `OAI.UniversalTensorSquare.sg30694`, `OAI.UniversalTensorSquare.sg30698`, `OAI.UniversalTensorSquare.sg30822`, `OAI.UniversalTensorSquare.sg31080`, `OAI.UniversalTensorSquare.sg31101`, `OAI.UniversalTensorSquare.sg31103`, `OAI.UniversalTensorSquare.sg31224`, `OAI.UniversalTensorSquare.sg31336`, `OAI.UniversalTensorSquare.sg31337`, `OAI.UniversalTensorSquare.sg31410`, `OAI.UniversalTensorSquare.sg31421` and `OAI.UniversalTensorSquare.sg31423` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes20.lean (declaration OAI.UniversalTensorSquare.sg8721)

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

lemma sg8721 : RowSquare [6,6,2,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
