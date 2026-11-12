-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg2710
-- name    : OAI.UniversalTensorSquare.sg2710
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:57:48.780371+00:00
-- url     : https://prove2.me/theorems/aa6d7a62-11bf-4764-bae4-9276bfc1a298
-- title:
--   OAI.UniversalTensorSquare.sg2710: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg2710` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg2710 : RowSquare [7,2,1,1,1,1,1] [3,2,2,2,2,2,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_323All`, `OAI.UniversalTensorSquare.degreeTree62_326All`, `OAI.UniversalTensorSquare.degreeTree62_328All`, `OAI.UniversalTensorSquare.degreeTree62_336All`, `OAI.UniversalTensorSquare.degreeTree62_344All`, `OAI.UniversalTensorSquare.degreeTree62_348All`, `OAI.UniversalTensorSquare.degreeTree62_349All`, `OAI.UniversalTensorSquare.degreeTree62_351All`, `OAI.UniversalTensorSquare.degreeTree62_364All`, `OAI.UniversalTensorSquare.degreeTree62_366All`, `OAI.UniversalTensorSquare.degreeTree62_367All`, `OAI.UniversalTensorSquare.degreeTree62_374All`, `OAI.UniversalTensorSquare.degreeTree62_394All`, `OAI.UniversalTensorSquare.degreeTree62_3All`, `OAI.UniversalTensorSquare.degreeTree62_405All`, `OAI.UniversalTensorSquare.degreeTree62_413All`, `OAI.UniversalTensorSquare.degreeTree62_414All`, `OAI.UniversalTensorSquare.degreeTree62_430All`, `OAI.UniversalTensorSquare.degreeTree62_434All`, `OAI.UniversalTensorSquare.degreeTree62_444All`, `OAI.UniversalTensorSquare.degreeTree62_445All`, `OAI.UniversalTensorSquare.degreeTree62_450All`, `OAI.UniversalTensorSquare.degreeTree62_454All`, `OAI.UniversalTensorSquare.degreeTree62_465All`, `OAI.UniversalTensorSquare.degreeTree62_475All`, `OAI.UniversalTensorSquare.degreeTree62_521All`, `OAI.UniversalTensorSquare.degreeTree62_537All`, `OAI.UniversalTensorSquare.degreeTree62_546All`, `OAI.UniversalTensorSquare.degreeTree62_553All`, `OAI.UniversalTensorSquare.degreeTree62_565All`, `OAI.UniversalTensorSquare.degreeTree62_569All`, `OAI.UniversalTensorSquare.degreeTree62_584All`, `OAI.UniversalTensorSquare.degreeTree62_629All`, `OAI.UniversalTensorSquare.degreeTree62_640All`, `OAI.UniversalTensorSquare.degreeTree62_648All`, `OAI.UniversalTensorSquare.degreeTree62_656All`, `OAI.UniversalTensorSquare.degreeTree62_673All`, `OAI.UniversalTensorSquare.degreeTree62_758All`, `OAI.UniversalTensorSquare.degreeTree62_760All`, `OAI.UniversalTensorSquare.degreeTree62_768All`, `OAI.UniversalTensorSquare.degreeTree62_771All`, `OAI.UniversalTensorSquare.degreeTree62_77All`, `OAI.UniversalTensorSquare.degreeTree62_801All`, `OAI.UniversalTensorSquare.degreeTree62_809All`, `OAI.UniversalTensorSquare.degreeTree62_826All`, `OAI.UniversalTensorSquare.degreeTree62_829All`, `OAI.UniversalTensorSquare.degreeTree62_871All`, `OAI.UniversalTensorSquare.degreeTree62_872All`, `OAI.UniversalTensorSquare.degreeTree62_889All`, `OAI.UniversalTensorSquare.degreeTree62_955All`, `OAI.UniversalTensorSquare.sg10843`, `OAI.UniversalTensorSquare.sg19049`, `OAI.UniversalTensorSquare.sg19111`, `OAI.UniversalTensorSquare.sg19129`, `OAI.UniversalTensorSquare.sg19153`, `OAI.UniversalTensorSquare.sg19155`, `OAI.UniversalTensorSquare.sg19176`, `OAI.UniversalTensorSquare.sg20254`, `OAI.UniversalTensorSquare.sg20306`, `OAI.UniversalTensorSquare.sg32720`, `OAI.UniversalTensorSquare.sg32740`, `OAI.UniversalTensorSquare.sg32812`, `OAI.UniversalTensorSquare.sg32886`, `OAI.UniversalTensorSquare.sg33200`, `OAI.UniversalTensorSquare.sg35794`, `OAI.UniversalTensorSquare.sg35799`, `OAI.UniversalTensorSquare.sg35941`, `OAI.UniversalTensorSquare.sg35946`, `OAI.UniversalTensorSquare.sg36002`, `OAI.UniversalTensorSquare.sg36012`, `OAI.UniversalTensorSquare.sg36014`, `OAI.UniversalTensorSquare.sg36016`, `OAI.UniversalTensorSquare.sg36099`, `OAI.UniversalTensorSquare.sg36103`, `OAI.UniversalTensorSquare.sg36170`, `OAI.UniversalTensorSquare.sg36175`, `OAI.UniversalTensorSquare.sg36177`, `OAI.UniversalTensorSquare.sg36179`, `OAI.UniversalTensorSquare.sg36242`, `OAI.UniversalTensorSquare.sg36246`, `OAI.UniversalTensorSquare.sg36356`, `OAI.UniversalTensorSquare.sg36357`, `OAI.UniversalTensorSquare.sg36387`, `OAI.UniversalTensorSquare.sg36389`, `OAI.UniversalTensorSquare.sg36451`, `OAI.UniversalTensorSquare.sg36456`, `OAI.UniversalTensorSquare.sg36525`, `OAI.UniversalTensorSquare.sg36616`, `OAI.UniversalTensorSquare.sg36671`, `OAI.UniversalTensorSquare.sg36681`, `OAI.UniversalTensorSquare.sg36683`, `OAI.UniversalTensorSquare.sg36685`, `OAI.UniversalTensorSquare.sg36751`, `OAI.UniversalTensorSquare.sg36756`, `OAI.UniversalTensorSquare.sg36758`, `OAI.UniversalTensorSquare.sg36760`, `OAI.UniversalTensorSquare.sg36768`, `OAI.UniversalTensorSquare.sg36820`, `OAI.UniversalTensorSquare.sg36824`, `OAI.UniversalTensorSquare.sg36993`, `OAI.UniversalTensorSquare.sg36995`, `OAI.UniversalTensorSquare.sg37139`, `OAI.UniversalTensorSquare.sg37144`, `OAI.UniversalTensorSquare.sg37146`, `OAI.UniversalTensorSquare.sg37148`, `OAI.UniversalTensorSquare.sg37236`, `OAI.UniversalTensorSquare.sg37240`, `OAI.UniversalTensorSquare.sg37511`, `OAI.UniversalTensorSquare.sg37820`, `OAI.UniversalTensorSquare.sg37829`, `OAI.UniversalTensorSquare.sg37831`, `OAI.UniversalTensorSquare.sg37833`, `OAI.UniversalTensorSquare.sg37890`, `OAI.UniversalTensorSquare.sg37895`, `OAI.UniversalTensorSquare.sg37897`, `OAI.UniversalTensorSquare.sg37899`, `OAI.UniversalTensorSquare.sg38040`, `OAI.UniversalTensorSquare.sg38045`, `OAI.UniversalTensorSquare.sg38047`, `OAI.UniversalTensorSquare.sg38049`, `OAI.UniversalTensorSquare.sg38186`, `OAI.UniversalTensorSquare.sg38281`, `OAI.UniversalTensorSquare.sg38379`, `OAI.UniversalTensorSquare.sg38466`, `OAI.UniversalTensorSquare.sg38552`, `OAI.UniversalTensorSquare.sg39625`, `OAI.UniversalTensorSquare.sg40514`, `OAI.UniversalTensorSquare.sg40783`, `OAI.UniversalTensorSquare.sg40894`, `OAI.UniversalTensorSquare.sg41074`, `OAI.UniversalTensorSquare.sg41532`, `OAI.UniversalTensorSquare.sg41571`, `OAI.UniversalTensorSquare.sg41734`, `OAI.UniversalTensorSquare.sg42148`, `OAI.UniversalTensorSquare.sg42198`, `OAI.UniversalTensorSquare.sg42838`, `OAI.UniversalTensorSquare.sg42839` and `OAI.UniversalTensorSquare.sg42848` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes5.lean (declaration OAI.UniversalTensorSquare.sg2710)

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

lemma sg2710 : RowSquare [7,2,1,1,1,1,1] [3,2,2,2,2,2,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
