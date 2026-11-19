-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg840
-- name    : OAI.UniversalTensorSquare.sg840
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T23:39:05.023635+00:00
-- url     : https://prove2.me/theorems/c13026d7-f043-4cbe-a1cc-ce583261a3c7
-- title:
--   OAI.UniversalTensorSquare.sg840: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg840` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg840 : RowSquare [4,3,1,1,1] [2,2,2,2,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_675All`, `OAI.UniversalTensorSquare.sg34281`, `OAI.UniversalTensorSquare.sg34291`, `OAI.UniversalTensorSquare.sg34294`, `OAI.UniversalTensorSquare.sg34296`, `OAI.UniversalTensorSquare.sg34676`, `OAI.UniversalTensorSquare.sg34698`, `OAI.UniversalTensorSquare.sg34701`, `OAI.UniversalTensorSquare.sg34814`, `OAI.UniversalTensorSquare.sg34817`, `OAI.UniversalTensorSquare.sg34819`, `OAI.UniversalTensorSquare.sg34949`, `OAI.UniversalTensorSquare.sg34959`, `OAI.UniversalTensorSquare.sg34962`, `OAI.UniversalTensorSquare.sg34964`, `OAI.UniversalTensorSquare.sg37411`, `OAI.UniversalTensorSquare.sg37421`, `OAI.UniversalTensorSquare.sg37424`, `OAI.UniversalTensorSquare.sg37426`, `OAI.UniversalTensorSquare.sg37528`, `OAI.UniversalTensorSquare.sg37549`, `OAI.UniversalTensorSquare.sg37552`, `OAI.UniversalTensorSquare.sg37568`, `OAI.UniversalTensorSquare.sg37578`, `OAI.UniversalTensorSquare.sg37581`, `OAI.UniversalTensorSquare.sg37583`, `OAI.UniversalTensorSquare.sg38099`, `OAI.UniversalTensorSquare.sg38120`, `OAI.UniversalTensorSquare.sg38123`, `OAI.UniversalTensorSquare.sg38125`, `OAI.UniversalTensorSquare.sg38288`, `OAI.UniversalTensorSquare.sg38298`, `OAI.UniversalTensorSquare.sg38301`, `OAI.UniversalTensorSquare.sg38303`, `OAI.UniversalTensorSquare.sg38789`, `OAI.UniversalTensorSquare.sg38799`, `OAI.UniversalTensorSquare.sg38802`, `OAI.UniversalTensorSquare.sg39107`, `OAI.UniversalTensorSquare.sg39110`, `OAI.UniversalTensorSquare.sg39112`, `OAI.UniversalTensorSquare.sg39296`, `OAI.UniversalTensorSquare.sg39314`, `OAI.UniversalTensorSquare.sg39317`, `OAI.UniversalTensorSquare.sg39318`, `OAI.UniversalTensorSquare.sg39400`, `OAI.UniversalTensorSquare.sg39421`, `OAI.UniversalTensorSquare.sg39422`, `OAI.UniversalTensorSquare.sg39432`, `OAI.UniversalTensorSquare.sg39442`, `OAI.UniversalTensorSquare.sg39445`, `OAI.UniversalTensorSquare.sg39446`, `OAI.UniversalTensorSquare.sg39661`, `OAI.UniversalTensorSquare.sg39664`, `OAI.UniversalTensorSquare.sg39665`, `OAI.UniversalTensorSquare.sg40149`, `OAI.UniversalTensorSquare.sg40165`, `OAI.UniversalTensorSquare.sg40167`, `OAI.UniversalTensorSquare.sg40168`, `OAI.UniversalTensorSquare.sg40708`, `OAI.UniversalTensorSquare.sg40724`, `OAI.UniversalTensorSquare.sg40726`, `OAI.UniversalTensorSquare.sg40727`, `OAI.UniversalTensorSquare.sg41134`, `OAI.UniversalTensorSquare.sg41143`, `OAI.UniversalTensorSquare.sg41145`, `OAI.UniversalTensorSquare.sg41146`, `OAI.UniversalTensorSquare.sg42824`, `OAI.UniversalTensorSquare.sg42825`, `OAI.UniversalTensorSquare.sg42900`, `OAI.UniversalTensorSquare.sg42901`, `OAI.UniversalTensorSquare.sg42961`, `OAI.UniversalTensorSquare.sg42962`, `OAI.UniversalTensorSquare.sg42989`, `OAI.UniversalTensorSquare.sg42990`, `OAI.UniversalTensorSquare.sg43072`, `OAI.UniversalTensorSquare.sg43073`, `OAI.UniversalTensorSquare.sg43117`, `OAI.UniversalTensorSquare.sg43132`, `OAI.UniversalTensorSquare.sg43170`, `OAI.UniversalTensorSquare.sg43181`, `OAI.UniversalTensorSquare.sg43193`, `OAI.UniversalTensorSquare.sg6309`, `OAI.UniversalTensorSquare.sg7243`, `OAI.UniversalTensorSquare.sg7908`, `OAI.UniversalTensorSquare.sg7909` and `OAI.UniversalTensorSquare.sg9245` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean (declaration OAI.UniversalTensorSquare.sg840)

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

lemma sg840 : RowSquare [4,3,1,1,1] [2,2,2,2,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
