-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg202
-- name    : OAI.UniversalTensorSquare.sg202
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:49:55.403692+00:00
-- url     : https://prove2.me/theorems/67ee7c6b-143a-4e49-862b-1fd177411a32
-- title:
--   OAI.UniversalTensorSquare.sg202: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg202` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg202 : RowSquare [4,2,1] [4,3]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_114All`, `OAI.UniversalTensorSquare.degreeTree62_129All`, `OAI.UniversalTensorSquare.degreeTree62_131All`, `OAI.UniversalTensorSquare.degreeTree62_133All`, `OAI.UniversalTensorSquare.degreeTree62_136All`, `OAI.UniversalTensorSquare.degreeTree62_137All`, `OAI.UniversalTensorSquare.degreeTree62_140All`, `OAI.UniversalTensorSquare.degreeTree62_146All`, `OAI.UniversalTensorSquare.degreeTree62_166All`, `OAI.UniversalTensorSquare.degreeTree62_16All`, `OAI.UniversalTensorSquare.degreeTree62_170All`, `OAI.UniversalTensorSquare.degreeTree62_173All`, `OAI.UniversalTensorSquare.degreeTree62_174All`, `OAI.UniversalTensorSquare.degreeTree62_199All`, `OAI.UniversalTensorSquare.degreeTree62_205All`, `OAI.UniversalTensorSquare.degreeTree62_209All`, `OAI.UniversalTensorSquare.degreeTree62_221All`, `OAI.UniversalTensorSquare.degreeTree62_225All`, `OAI.UniversalTensorSquare.degreeTree62_227All`, `OAI.UniversalTensorSquare.degreeTree62_230All`, `OAI.UniversalTensorSquare.degreeTree62_238All`, `OAI.UniversalTensorSquare.degreeTree62_255All`, `OAI.UniversalTensorSquare.degreeTree62_261All`, `OAI.UniversalTensorSquare.degreeTree62_266All`, `OAI.UniversalTensorSquare.degreeTree62_270All`, `OAI.UniversalTensorSquare.degreeTree62_271All`, `OAI.UniversalTensorSquare.degreeTree62_283All`, `OAI.UniversalTensorSquare.degreeTree62_287All`, `OAI.UniversalTensorSquare.degreeTree62_290All`, `OAI.UniversalTensorSquare.degreeTree62_294All`, `OAI.UniversalTensorSquare.degreeTree62_298All`, `OAI.UniversalTensorSquare.degreeTree62_304All`, `OAI.UniversalTensorSquare.degreeTree62_306All`, `OAI.UniversalTensorSquare.degreeTree62_310All`, `OAI.UniversalTensorSquare.degreeTree62_31All`, `OAI.UniversalTensorSquare.degreeTree62_42All`, `OAI.UniversalTensorSquare.degreeTree62_47All`, `OAI.UniversalTensorSquare.degreeTree62_533All`, `OAI.UniversalTensorSquare.degreeTree62_55All`, `OAI.UniversalTensorSquare.degreeTree62_62All`, `OAI.UniversalTensorSquare.degreeTree62_645All`, `OAI.UniversalTensorSquare.degreeTree62_665All`, `OAI.UniversalTensorSquare.degreeTree62_700All`, `OAI.UniversalTensorSquare.degreeTree62_736All`, `OAI.UniversalTensorSquare.degreeTree62_786All`, `OAI.UniversalTensorSquare.degreeTree62_813All`, `OAI.UniversalTensorSquare.degreeTree62_8All`, `OAI.UniversalTensorSquare.sg17197`, `OAI.UniversalTensorSquare.sg19572`, `OAI.UniversalTensorSquare.sg30704`, `OAI.UniversalTensorSquare.sg30706`, `OAI.UniversalTensorSquare.sg30707`, `OAI.UniversalTensorSquare.sg30708`, `OAI.UniversalTensorSquare.sg30709`, `OAI.UniversalTensorSquare.sg32022`, `OAI.UniversalTensorSquare.sg32182`, `OAI.UniversalTensorSquare.sg32411`, `OAI.UniversalTensorSquare.sg32482`, `OAI.UniversalTensorSquare.sg32489`, `OAI.UniversalTensorSquare.sg32498`, `OAI.UniversalTensorSquare.sg32509`, `OAI.UniversalTensorSquare.sg32522`, `OAI.UniversalTensorSquare.sg32534`, `OAI.UniversalTensorSquare.sg32566`, `OAI.UniversalTensorSquare.sg32569`, `OAI.UniversalTensorSquare.sg32579`, `OAI.UniversalTensorSquare.sg32582`, `OAI.UniversalTensorSquare.sg32608`, `OAI.UniversalTensorSquare.sg32611`, `OAI.UniversalTensorSquare.sg32615`, `OAI.UniversalTensorSquare.sg32618`, `OAI.UniversalTensorSquare.sg32627`, `OAI.UniversalTensorSquare.sg32653`, `OAI.UniversalTensorSquare.sg32683`, `OAI.UniversalTensorSquare.sg32745`, `OAI.UniversalTensorSquare.sg32796`, `OAI.UniversalTensorSquare.sg33120`, `OAI.UniversalTensorSquare.sg33209`, `OAI.UniversalTensorSquare.sg33373`, `OAI.UniversalTensorSquare.sg33507`, `OAI.UniversalTensorSquare.sg33510`, `OAI.UniversalTensorSquare.sg33567`, `OAI.UniversalTensorSquare.sg33570`, `OAI.UniversalTensorSquare.sg33590`, `OAI.UniversalTensorSquare.sg33828`, `OAI.UniversalTensorSquare.sg33841`, `OAI.UniversalTensorSquare.sg33930`, `OAI.UniversalTensorSquare.sg34501`, `OAI.UniversalTensorSquare.sg34560`, `OAI.UniversalTensorSquare.sg34583`, `OAI.UniversalTensorSquare.sg34639`, `OAI.UniversalTensorSquare.sg34692`, `OAI.UniversalTensorSquare.sg34789`, `OAI.UniversalTensorSquare.sg34873`, `OAI.UniversalTensorSquare.sg35004`, `OAI.UniversalTensorSquare.sg35064`, `OAI.UniversalTensorSquare.sg35118`, `OAI.UniversalTensorSquare.sg35136`, `OAI.UniversalTensorSquare.sg35282`, `OAI.UniversalTensorSquare.sg35346`, `OAI.UniversalTensorSquare.sg35398`, `OAI.UniversalTensorSquare.sg35415`, `OAI.UniversalTensorSquare.sg36852`, `OAI.UniversalTensorSquare.sg37163`, `OAI.UniversalTensorSquare.sg37886`, `OAI.UniversalTensorSquare.sg37904`, `OAI.UniversalTensorSquare.sg38061`, `OAI.UniversalTensorSquare.sg38401`, `OAI.UniversalTensorSquare.sg39056`, `OAI.UniversalTensorSquare.sg39103`, `OAI.UniversalTensorSquare.sg40067`, `OAI.UniversalTensorSquare.sg40132`, `OAI.UniversalTensorSquare.sg40144`, `OAI.UniversalTensorSquare.sg41200`, `OAI.UniversalTensorSquare.sg41579`, `OAI.UniversalTensorSquare.sg41659`, `OAI.UniversalTensorSquare.sg8430` and `OAI.UniversalTensorSquare.sg8466` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean (declaration OAI.UniversalTensorSquare.sg202)

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

lemma sg202 : RowSquare [4,2,1] [4,3] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
