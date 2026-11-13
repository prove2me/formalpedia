-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg6457
-- name    : OAI.UniversalTensorSquare.sg6457
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:25:34.561211+00:00
-- url     : https://prove2.me/theorems/68cae782-9930-4078-b560-92ef6ffe7332
-- title:
--   OAI.UniversalTensorSquare.sg6457: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg6457` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg6457 : RowSquare [6,5,3,2,2,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_55All`, `OAI.UniversalTensorSquare.degreeTree39_56All`, `OAI.UniversalTensorSquare.degreeTree39_65All`, `OAI.UniversalTensorSquare.degreeTree39_66All`, `OAI.UniversalTensorSquare.degreeTree39_67All`, `OAI.UniversalTensorSquare.degreeTree39_72All`, `OAI.UniversalTensorSquare.degreeTree39_73All`, `OAI.UniversalTensorSquare.degreeTree39_83All`, `OAI.UniversalTensorSquare.degreeTree39_87All`, `OAI.UniversalTensorSquare.degreeTree43_168All`, `OAI.UniversalTensorSquare.degreeTree43_177All`, `OAI.UniversalTensorSquare.degreeTree43_184All`, `OAI.UniversalTensorSquare.degreeTree43_207All`, `OAI.UniversalTensorSquare.degreeTree43_209All`, `OAI.UniversalTensorSquare.degreeTree43_215All`, `OAI.UniversalTensorSquare.degreeTree43_226All`, `OAI.UniversalTensorSquare.degreeTree43_228All`, `OAI.UniversalTensorSquare.degreeTree43_260All`, `OAI.UniversalTensorSquare.degreeTree43_263All`, `OAI.UniversalTensorSquare.degreeTree43_269All`, `OAI.UniversalTensorSquare.degreeTree43_273All`, `OAI.UniversalTensorSquare.degreeTree43_285All`, `OAI.UniversalTensorSquare.degreeTree43_286All`, `OAI.UniversalTensorSquare.degreeTree43_290All`, `OAI.UniversalTensorSquare.degreeTree43_357All`, `OAI.UniversalTensorSquare.degreeTree43_362All`, `OAI.UniversalTensorSquare.degreeTree43_380All`, `OAI.UniversalTensorSquare.degreeTree43_389All`, `OAI.UniversalTensorSquare.degreeTree43_392All`, `OAI.UniversalTensorSquare.degreeTree43_394All`, `OAI.UniversalTensorSquare.degreeTree43_397All`, `OAI.UniversalTensorSquare.degreeTree43_409All`, `OAI.UniversalTensorSquare.degreeTree43_411All`, `OAI.UniversalTensorSquare.degreeTree43_417All`, `OAI.UniversalTensorSquare.degreeTree43_420All`, `OAI.UniversalTensorSquare.degreeTree43_435All`, `OAI.UniversalTensorSquare.degreeTree43_441All`, `OAI.UniversalTensorSquare.degreeTree43_446All`, `OAI.UniversalTensorSquare.degreeTree43_457All`, `OAI.UniversalTensorSquare.degreeTree43_465All`, `OAI.UniversalTensorSquare.degreeTree43_476All`, `OAI.UniversalTensorSquare.degreeTree43_47All`, `OAI.UniversalTensorSquare.degreeTree43_481All`, `OAI.UniversalTensorSquare.degreeTree43_484All`, `OAI.UniversalTensorSquare.degreeTree43_495All`, `OAI.UniversalTensorSquare.degreeTree43_498All`, `OAI.UniversalTensorSquare.degreeTree43_500All`, `OAI.UniversalTensorSquare.degreeTree43_507All`, `OAI.UniversalTensorSquare.degreeTree43_513All`, `OAI.UniversalTensorSquare.degreeTree43_520All`, `OAI.UniversalTensorSquare.degreeTree43_521All`, `OAI.UniversalTensorSquare.degreeTree43_532All`, `OAI.UniversalTensorSquare.degreeTree43_551All`, `OAI.UniversalTensorSquare.degreeTree43_553All`, `OAI.UniversalTensorSquare.degreeTree43_556All`, `OAI.UniversalTensorSquare.degreeTree43_560All`, `OAI.UniversalTensorSquare.degreeTree43_561All`, `OAI.UniversalTensorSquare.degreeTree43_572All`, `OAI.UniversalTensorSquare.degreeTree43_586All`, `OAI.UniversalTensorSquare.degreeTree43_593All`, `OAI.UniversalTensorSquare.degreeTree43_84All`, `OAI.UniversalTensorSquare.degreeTree43_88All`, `OAI.UniversalTensorSquare.degreeTree43_93All`, `OAI.UniversalTensorSquare.sg14718`, `OAI.UniversalTensorSquare.sg14723`, `OAI.UniversalTensorSquare.sg22326`, `OAI.UniversalTensorSquare.sg22491`, `OAI.UniversalTensorSquare.sg22518`, `OAI.UniversalTensorSquare.sg22525`, `OAI.UniversalTensorSquare.sg22558`, `OAI.UniversalTensorSquare.sg22637`, `OAI.UniversalTensorSquare.sg22663`, `OAI.UniversalTensorSquare.sg22677`, `OAI.UniversalTensorSquare.sg22759`, `OAI.UniversalTensorSquare.sg22938`, `OAI.UniversalTensorSquare.sg23022`, `OAI.UniversalTensorSquare.sg23030`, `OAI.UniversalTensorSquare.sg23132`, `OAI.UniversalTensorSquare.sg23520`, `OAI.UniversalTensorSquare.sg23554`, `OAI.UniversalTensorSquare.sg23588`, `OAI.UniversalTensorSquare.sg24754`, `OAI.UniversalTensorSquare.sg24770`, `OAI.UniversalTensorSquare.sg25081`, `OAI.UniversalTensorSquare.sg25089`, `OAI.UniversalTensorSquare.sg25118`, `OAI.UniversalTensorSquare.sg25926`, `OAI.UniversalTensorSquare.sg25951`, `OAI.UniversalTensorSquare.sg26319`, `OAI.UniversalTensorSquare.sg26552`, `OAI.UniversalTensorSquare.sg26779`, `OAI.UniversalTensorSquare.sg26787`, `OAI.UniversalTensorSquare.sg27041`, `OAI.UniversalTensorSquare.sg27069`, `OAI.UniversalTensorSquare.sg27158`, `OAI.UniversalTensorSquare.sg28234`, `OAI.UniversalTensorSquare.sg28323`, `OAI.UniversalTensorSquare.sg28572`, `OAI.UniversalTensorSquare.sg28765`, `OAI.UniversalTensorSquare.sg28917`, `OAI.UniversalTensorSquare.sg29215`, `OAI.UniversalTensorSquare.sg29288`, `OAI.UniversalTensorSquare.sg29389`, `OAI.UniversalTensorSquare.sg29450`, `OAI.UniversalTensorSquare.sg29547`, `OAI.UniversalTensorSquare.sg29554`, `OAI.UniversalTensorSquare.sg29579`, `OAI.UniversalTensorSquare.sg29761`, `OAI.UniversalTensorSquare.sg29991`, `OAI.UniversalTensorSquare.sg30068`, `OAI.UniversalTensorSquare.sg30148`, `OAI.UniversalTensorSquare.sg30173`, `OAI.UniversalTensorSquare.sg30297`, `OAI.UniversalTensorSquare.sg30463`, `OAI.UniversalTensorSquare.sg30599`, `OAI.UniversalTensorSquare.sg30714`, `OAI.UniversalTensorSquare.sg30731`, `OAI.UniversalTensorSquare.sg30777`, `OAI.UniversalTensorSquare.sg30861`, `OAI.UniversalTensorSquare.sg30988`, `OAI.UniversalTensorSquare.sg31126`, `OAI.UniversalTensorSquare.sg31135`, `OAI.UniversalTensorSquare.sg31249` and `OAI.UniversalTensorSquare.sg31343` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg6457)

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

lemma sg6457 : RowSquare [6,5,3,2,2,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
