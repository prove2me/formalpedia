-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg68
-- name    : OAI.UniversalTensorSquare.sg68
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T23:03:54.108297+00:00
-- url     : https://prove2.me/theorems/530c204f-8717-4cef-b3f1-24d6492c92b6
-- title:
--   OAI.UniversalTensorSquare.sg68: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg68` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg68 : RowSquare [3,1,1,1] [2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree26_18All`, `OAI.UniversalTensorSquare.degreeTree26_19All`, `OAI.UniversalTensorSquare.degreeTree26_24All`, `OAI.UniversalTensorSquare.degreeTree43_177All`, `OAI.UniversalTensorSquare.degreeTree43_185All`, `OAI.UniversalTensorSquare.degreeTree43_228All`, `OAI.UniversalTensorSquare.degreeTree43_234All`, `OAI.UniversalTensorSquare.degreeTree43_242All`, `OAI.UniversalTensorSquare.degreeTree43_305All`, `OAI.UniversalTensorSquare.degreeTree43_306All`, `OAI.UniversalTensorSquare.degreeTree43_544All`, `OAI.UniversalTensorSquare.degreeTree43_625All`, `OAI.UniversalTensorSquare.degreeTree43_630All`, `OAI.UniversalTensorSquare.degreeTree62_427All`, `OAI.UniversalTensorSquare.degreeTree62_471All`, `OAI.UniversalTensorSquare.degreeTree62_547All`, `OAI.UniversalTensorSquare.degreeTree62_680All`, `OAI.UniversalTensorSquare.degree_pos26`, `OAI.UniversalTensorSquare.sg12152`, `OAI.UniversalTensorSquare.sg14631`, `OAI.UniversalTensorSquare.sg15784`, `OAI.UniversalTensorSquare.sg15944`, `OAI.UniversalTensorSquare.sg21993`, `OAI.UniversalTensorSquare.sg22351`, `OAI.UniversalTensorSquare.sg22370`, `OAI.UniversalTensorSquare.sg22374`, `OAI.UniversalTensorSquare.sg24245`, `OAI.UniversalTensorSquare.sg24766`, `OAI.UniversalTensorSquare.sg24815`, `OAI.UniversalTensorSquare.sg24821`, `OAI.UniversalTensorSquare.sg25093`, `OAI.UniversalTensorSquare.sg25095`, `OAI.UniversalTensorSquare.sg26571`, `OAI.UniversalTensorSquare.sg26593`, `OAI.UniversalTensorSquare.sg26872`, `OAI.UniversalTensorSquare.sg26992`, `OAI.UniversalTensorSquare.sg27006`, `OAI.UniversalTensorSquare.sg27008`, `OAI.UniversalTensorSquare.sg27010`, `OAI.UniversalTensorSquare.sg27359`, `OAI.UniversalTensorSquare.sg29792`, `OAI.UniversalTensorSquare.sg31347`, `OAI.UniversalTensorSquare.sg33110`, `OAI.UniversalTensorSquare.sg33158`, `OAI.UniversalTensorSquare.sg34626`, `OAI.UniversalTensorSquare.sg34630`, `OAI.UniversalTensorSquare.sg34648`, `OAI.UniversalTensorSquare.sg34651`, `OAI.UniversalTensorSquare.sg34659`, `OAI.UniversalTensorSquare.sg34675`, `OAI.UniversalTensorSquare.sg34694`, `OAI.UniversalTensorSquare.sg34761`, `OAI.UniversalTensorSquare.sg34775`, `OAI.UniversalTensorSquare.sg34777`, `OAI.UniversalTensorSquare.sg34904`, `OAI.UniversalTensorSquare.sg34941`, `OAI.UniversalTensorSquare.sg35915`, `OAI.UniversalTensorSquare.sg35917`, `OAI.UniversalTensorSquare.sg35918`, `OAI.UniversalTensorSquare.sg35933`, `OAI.UniversalTensorSquare.sg36621`, `OAI.UniversalTensorSquare.sg37071`, `OAI.UniversalTensorSquare.sg37073`, `OAI.UniversalTensorSquare.sg37074`, `OAI.UniversalTensorSquare.sg37088`, `OAI.UniversalTensorSquare.sg37093`, `OAI.UniversalTensorSquare.sg37112`, `OAI.UniversalTensorSquare.sg37121`, `OAI.UniversalTensorSquare.sg37249`, `OAI.UniversalTensorSquare.sg37774`, `OAI.UniversalTensorSquare.sg37977`, `OAI.UniversalTensorSquare.sg37978`, `OAI.UniversalTensorSquare.sg37998`, `OAI.UniversalTensorSquare.sg38041`, `OAI.UniversalTensorSquare.sg38380`, `OAI.UniversalTensorSquare.sg38386`, `OAI.UniversalTensorSquare.sg38391`, `OAI.UniversalTensorSquare.sg38405`, `OAI.UniversalTensorSquare.sg38442`, `OAI.UniversalTensorSquare.sg38984`, `OAI.UniversalTensorSquare.sg39180`, `OAI.UniversalTensorSquare.sg39181`, `OAI.UniversalTensorSquare.sg39203`, `OAI.UniversalTensorSquare.sg39541`, `OAI.UniversalTensorSquare.sg39561`, `OAI.UniversalTensorSquare.sg4043`, `OAI.UniversalTensorSquare.sg40542`, `OAI.UniversalTensorSquare.sg40552`, `OAI.UniversalTensorSquare.sg40970`, `OAI.UniversalTensorSquare.sg41191`, `OAI.UniversalTensorSquare.sg41200`, `OAI.UniversalTensorSquare.sg41203`, `OAI.UniversalTensorSquare.sg41207`, `OAI.UniversalTensorSquare.sg41268`, `OAI.UniversalTensorSquare.sg41652`, `OAI.UniversalTensorSquare.sg41844`, `OAI.UniversalTensorSquare.sg41846`, `OAI.UniversalTensorSquare.sg41849`, `OAI.UniversalTensorSquare.sg41927`, `OAI.UniversalTensorSquare.sg42121`, `OAI.UniversalTensorSquare.sg42205`, `OAI.UniversalTensorSquare.sg42209`, `OAI.UniversalTensorSquare.sg42362`, `OAI.UniversalTensorSquare.sg42925`, `OAI.UniversalTensorSquare.sg4789`, `OAI.UniversalTensorSquare.sg5261`, `OAI.UniversalTensorSquare.sg543`, `OAI.UniversalTensorSquare.sg6119`, `OAI.UniversalTensorSquare.sg6315`, `OAI.UniversalTensorSquare.sg6685`, `OAI.UniversalTensorSquare.sg7351`, `OAI.UniversalTensorSquare.sg7360`, `OAI.UniversalTensorSquare.sg7362`, `OAI.UniversalTensorSquare.sg7401`, `OAI.UniversalTensorSquare.sg9319` and `OAI.UniversalTensorSquare.sg9320` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean (declaration OAI.UniversalTensorSquare.sg68)

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

lemma sg68 : RowSquare [3,1,1,1] [2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
