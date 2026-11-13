-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg7812
-- name    : OAI.UniversalTensorSquare.sg7812
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:39:41.151206+00:00
-- url     : https://prove2.me/theorems/d5bc263b-e7df-48a6-abd9-7406118cad92
-- title:
--   OAI.UniversalTensorSquare.sg7812: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg7812` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg7812 : RowSquare [6,6,2,2,2,2] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree41_2All`, `OAI.UniversalTensorSquare.degreeTree41_4All`, `OAI.UniversalTensorSquare.degreeTree43_109All`, `OAI.UniversalTensorSquare.degreeTree43_179All`, `OAI.UniversalTensorSquare.degreeTree43_209All`, `OAI.UniversalTensorSquare.degreeTree43_244All`, `OAI.UniversalTensorSquare.degreeTree43_258All`, `OAI.UniversalTensorSquare.degreeTree43_259All`, `OAI.UniversalTensorSquare.degreeTree43_263All`, `OAI.UniversalTensorSquare.degreeTree43_316All`, `OAI.UniversalTensorSquare.degreeTree43_320All`, `OAI.UniversalTensorSquare.degreeTree43_335All`, `OAI.UniversalTensorSquare.degreeTree43_340All`, `OAI.UniversalTensorSquare.degreeTree43_342All`, `OAI.UniversalTensorSquare.degreeTree43_343All`, `OAI.UniversalTensorSquare.degreeTree43_345All`, `OAI.UniversalTensorSquare.degreeTree43_351All`, `OAI.UniversalTensorSquare.degreeTree43_353All`, `OAI.UniversalTensorSquare.degreeTree43_357All`, `OAI.UniversalTensorSquare.degreeTree43_361All`, `OAI.UniversalTensorSquare.degreeTree43_362All`, `OAI.UniversalTensorSquare.degreeTree43_372All`, `OAI.UniversalTensorSquare.degreeTree43_377All`, `OAI.UniversalTensorSquare.degreeTree43_380All`, `OAI.UniversalTensorSquare.degreeTree43_389All`, `OAI.UniversalTensorSquare.degreeTree43_392All`, `OAI.UniversalTensorSquare.degreeTree43_397All`, `OAI.UniversalTensorSquare.degreeTree43_403All`, `OAI.UniversalTensorSquare.degreeTree43_409All`, `OAI.UniversalTensorSquare.degreeTree43_411All`, `OAI.UniversalTensorSquare.degreeTree43_417All`, `OAI.UniversalTensorSquare.degreeTree43_428All`, `OAI.UniversalTensorSquare.degreeTree43_431All`, `OAI.UniversalTensorSquare.degreeTree43_432All`, `OAI.UniversalTensorSquare.degreeTree43_433All`, `OAI.UniversalTensorSquare.degreeTree43_435All`, `OAI.UniversalTensorSquare.degreeTree43_441All`, `OAI.UniversalTensorSquare.degreeTree43_446All`, `OAI.UniversalTensorSquare.degreeTree43_450All`, `OAI.UniversalTensorSquare.degreeTree43_459All`, `OAI.UniversalTensorSquare.degreeTree43_481All`, `OAI.UniversalTensorSquare.degreeTree43_484All`, `OAI.UniversalTensorSquare.degreeTree43_492All`, `OAI.UniversalTensorSquare.degreeTree43_495All`, `OAI.UniversalTensorSquare.degreeTree43_497All`, `OAI.UniversalTensorSquare.degreeTree43_498All`, `OAI.UniversalTensorSquare.degreeTree43_500All`, `OAI.UniversalTensorSquare.degreeTree43_510All`, `OAI.UniversalTensorSquare.degreeTree43_532All`, `OAI.UniversalTensorSquare.degreeTree43_544All`, `OAI.UniversalTensorSquare.degreeTree43_549All`, `OAI.UniversalTensorSquare.degreeTree43_551All`, `OAI.UniversalTensorSquare.degreeTree43_572All`, `OAI.UniversalTensorSquare.degreeTree43_598All`, `OAI.UniversalTensorSquare.degreeTree43_637All`, `OAI.UniversalTensorSquare.sg12971`, `OAI.UniversalTensorSquare.sg23544`, `OAI.UniversalTensorSquare.sg24753`, `OAI.UniversalTensorSquare.sg24762`, `OAI.UniversalTensorSquare.sg24794`, `OAI.UniversalTensorSquare.sg25909`, `OAI.UniversalTensorSquare.sg25918`, `OAI.UniversalTensorSquare.sg26302`, `OAI.UniversalTensorSquare.sg26311`, `OAI.UniversalTensorSquare.sg26551`, `OAI.UniversalTensorSquare.sg26559`, `OAI.UniversalTensorSquare.sg27032`, `OAI.UniversalTensorSquare.sg27068`, `OAI.UniversalTensorSquare.sg27141`, `OAI.UniversalTensorSquare.sg27150`, `OAI.UniversalTensorSquare.sg27182`, `OAI.UniversalTensorSquare.sg27317`, `OAI.UniversalTensorSquare.sg27325`, `OAI.UniversalTensorSquare.sg27770`, `OAI.UniversalTensorSquare.sg27810`, `OAI.UniversalTensorSquare.sg27818`, `OAI.UniversalTensorSquare.sg27846`, `OAI.UniversalTensorSquare.sg28001`, `OAI.UniversalTensorSquare.sg28038`, `OAI.UniversalTensorSquare.sg28047`, `OAI.UniversalTensorSquare.sg28079`, `OAI.UniversalTensorSquare.sg28153`, `OAI.UniversalTensorSquare.sg28162`, `OAI.UniversalTensorSquare.sg28196`, `OAI.UniversalTensorSquare.sg28233`, `OAI.UniversalTensorSquare.sg28491`, `OAI.UniversalTensorSquare.sg28500`, `OAI.UniversalTensorSquare.sg28507`, `OAI.UniversalTensorSquare.sg28542`, `OAI.UniversalTensorSquare.sg28571`, `OAI.UniversalTensorSquare.sg28627`, `OAI.UniversalTensorSquare.sg28676`, `OAI.UniversalTensorSquare.sg28873`, `OAI.UniversalTensorSquare.sg29177`, `OAI.UniversalTensorSquare.sg29204`, `OAI.UniversalTensorSquare.sg29222`, `OAI.UniversalTensorSquare.sg29261`, `OAI.UniversalTensorSquare.sg29345`, `OAI.UniversalTensorSquare.sg29537`, `OAI.UniversalTensorSquare.sg29546`, `OAI.UniversalTensorSquare.sg29983`, `OAI.UniversalTensorSquare.sg30024`, `OAI.UniversalTensorSquare.sg30131`, `OAI.UniversalTensorSquare.sg30140`, `OAI.UniversalTensorSquare.sg30296`, `OAI.UniversalTensorSquare.sg30304`, `OAI.UniversalTensorSquare.sg30722`, `OAI.UniversalTensorSquare.sg30760`, `OAI.UniversalTensorSquare.sg30769`, `OAI.UniversalTensorSquare.sg30801`, `OAI.UniversalTensorSquare.sg30860`, `OAI.UniversalTensorSquare.sg30868`, `OAI.UniversalTensorSquare.sg31125`, `OAI.UniversalTensorSquare.sg31134`, `OAI.UniversalTensorSquare.sg31168`, `OAI.UniversalTensorSquare.sg31176`, `OAI.UniversalTensorSquare.sg31248`, `OAI.UniversalTensorSquare.sg31788`, `OAI.UniversalTensorSquare.sg31794` and `OAI.UniversalTensorSquare.sg31891` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg7812)

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

lemma sg7812 : RowSquare [6,6,2,2,2,2] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
