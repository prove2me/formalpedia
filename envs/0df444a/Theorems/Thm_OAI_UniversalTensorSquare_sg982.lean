-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg982
-- name    : OAI.UniversalTensorSquare.sg982
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-18T00:11:15.211532+00:00
-- url     : https://prove2.me/theorems/c40a1c08-b367-47e1-886a-75826a08f275
-- title:
--   OAI.UniversalTensorSquare.sg982: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg982` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg982 : RowSquare [5,4,1] [2,2,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_348All`, `OAI.UniversalTensorSquare.degreeTree43_394All`, `OAI.UniversalTensorSquare.degreeTree62_28All`, `OAI.UniversalTensorSquare.sg20788`, `OAI.UniversalTensorSquare.sg27846`, `OAI.UniversalTensorSquare.sg27847`, `OAI.UniversalTensorSquare.sg28368`, `OAI.UniversalTensorSquare.sg36277`, `OAI.UniversalTensorSquare.sg36287`, `OAI.UniversalTensorSquare.sg36290`, `OAI.UniversalTensorSquare.sg36292`, `OAI.UniversalTensorSquare.sg36886`, `OAI.UniversalTensorSquare.sg36889`, `OAI.UniversalTensorSquare.sg36891`, `OAI.UniversalTensorSquare.sg37568`, `OAI.UniversalTensorSquare.sg37578`, `OAI.UniversalTensorSquare.sg37581`, `OAI.UniversalTensorSquare.sg37583`, `OAI.UniversalTensorSquare.sg37618`, `OAI.UniversalTensorSquare.sg37622`, `OAI.UniversalTensorSquare.sg37625`, `OAI.UniversalTensorSquare.sg37627`, `OAI.UniversalTensorSquare.sg37914`, `OAI.UniversalTensorSquare.sg37917`, `OAI.UniversalTensorSquare.sg37919`, `OAI.UniversalTensorSquare.sg38139`, `OAI.UniversalTensorSquare.sg38149`, `OAI.UniversalTensorSquare.sg38152`, `OAI.UniversalTensorSquare.sg38154`, `OAI.UniversalTensorSquare.sg38288`, `OAI.UniversalTensorSquare.sg38298`, `OAI.UniversalTensorSquare.sg38301`, `OAI.UniversalTensorSquare.sg38303`, `OAI.UniversalTensorSquare.sg38339`, `OAI.UniversalTensorSquare.sg38346`, `OAI.UniversalTensorSquare.sg38348`, `OAI.UniversalTensorSquare.sg39083`, `OAI.UniversalTensorSquare.sg39086`, `OAI.UniversalTensorSquare.sg39088`, `OAI.UniversalTensorSquare.sg39294`, `OAI.UniversalTensorSquare.sg39304`, `OAI.UniversalTensorSquare.sg39307`, `OAI.UniversalTensorSquare.sg39308`, `OAI.UniversalTensorSquare.sg39432`, `OAI.UniversalTensorSquare.sg39442`, `OAI.UniversalTensorSquare.sg39445`, `OAI.UniversalTensorSquare.sg39446`, `OAI.UniversalTensorSquare.sg39473`, `OAI.UniversalTensorSquare.sg39477`, `OAI.UniversalTensorSquare.sg39480`, `OAI.UniversalTensorSquare.sg39481`, `OAI.UniversalTensorSquare.sg40676`, `OAI.UniversalTensorSquare.sg40678`, `OAI.UniversalTensorSquare.sg40679`, `OAI.UniversalTensorSquare.sg40905`, `OAI.UniversalTensorSquare.sg40916`, `OAI.UniversalTensorSquare.sg40917`, `OAI.UniversalTensorSquare.sg40918`, `OAI.UniversalTensorSquare.sg41315`, `OAI.UniversalTensorSquare.sg41616`, `OAI.UniversalTensorSquare.sg41625`, `OAI.UniversalTensorSquare.sg41627`, `OAI.UniversalTensorSquare.sg41755`, `OAI.UniversalTensorSquare.sg42906`, `OAI.UniversalTensorSquare.sg42914`, `OAI.UniversalTensorSquare.sg43009`, `OAI.UniversalTensorSquare.sg43018`, `OAI.UniversalTensorSquare.sg43122`, `OAI.UniversalTensorSquare.sg43136`, `OAI.UniversalTensorSquare.sg43143`, `OAI.UniversalTensorSquare.sg43167`, `OAI.UniversalTensorSquare.sg43168`, `OAI.UniversalTensorSquare.sg43178`, `OAI.UniversalTensorSquare.sg43221`, `OAI.UniversalTensorSquare.sg8040`, `OAI.UniversalTensorSquare.sg8047`, `OAI.UniversalTensorSquare.sg8064` and `OAI.UniversalTensorSquare.sg8067` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean (declaration OAI.UniversalTensorSquare.sg982)

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

lemma sg982 : RowSquare [5,4,1] [2,2,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
