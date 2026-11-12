-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg19623
-- name    : OAI.UniversalTensorSquare.sg19623
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:48:02.424216+00:00
-- url     : https://prove2.me/theorems/f2d8692c-96f7-4240-9157-4f7f0132324c
-- title:
--   OAI.UniversalTensorSquare.sg19623: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg19623` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes47.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes47.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg19623 : RowSquare [8,6,4,3,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,3,2,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_152All`, `OAI.UniversalTensorSquare.degreeTree62_166All`, `OAI.UniversalTensorSquare.degreeTree62_191All`, `OAI.UniversalTensorSquare.degreeTree62_199All`, `OAI.UniversalTensorSquare.degreeTree62_210All`, `OAI.UniversalTensorSquare.degreeTree62_434All`, `OAI.UniversalTensorSquare.degreeTree62_445All`, `OAI.UniversalTensorSquare.degreeTree62_450All`, `OAI.UniversalTensorSquare.degreeTree62_537All`, `OAI.UniversalTensorSquare.degreeTree62_553All`, `OAI.UniversalTensorSquare.degreeTree62_565All`, `OAI.UniversalTensorSquare.degreeTree62_569All`, `OAI.UniversalTensorSquare.degreeTree62_584All`, `OAI.UniversalTensorSquare.degreeTree62_601All`, `OAI.UniversalTensorSquare.degreeTree62_602All`, `OAI.UniversalTensorSquare.degreeTree62_604All`, `OAI.UniversalTensorSquare.degreeTree62_615All`, `OAI.UniversalTensorSquare.degreeTree62_617All`, `OAI.UniversalTensorSquare.degreeTree62_648All`, `OAI.UniversalTensorSquare.degreeTree62_656All`, `OAI.UniversalTensorSquare.degreeTree62_664All`, `OAI.UniversalTensorSquare.degreeTree62_665All`, `OAI.UniversalTensorSquare.degreeTree62_672All`, `OAI.UniversalTensorSquare.degreeTree62_673All`, `OAI.UniversalTensorSquare.degreeTree62_677All`, `OAI.UniversalTensorSquare.degreeTree62_692All`, `OAI.UniversalTensorSquare.degreeTree62_694All`, `OAI.UniversalTensorSquare.degreeTree62_705All`, `OAI.UniversalTensorSquare.degreeTree62_709All`, `OAI.UniversalTensorSquare.degreeTree62_714All`, `OAI.UniversalTensorSquare.degreeTree62_716All`, `OAI.UniversalTensorSquare.degreeTree62_719All`, `OAI.UniversalTensorSquare.degreeTree62_733All`, `OAI.UniversalTensorSquare.degreeTree62_739All`, `OAI.UniversalTensorSquare.degreeTree62_742All`, `OAI.UniversalTensorSquare.degreeTree62_809All`, `OAI.UniversalTensorSquare.degreeTree62_823All`, `OAI.UniversalTensorSquare.degreeTree62_826All`, `OAI.UniversalTensorSquare.degreeTree62_829All`, `OAI.UniversalTensorSquare.degreeTree62_871All`, `OAI.UniversalTensorSquare.degreeTree62_872All`, `OAI.UniversalTensorSquare.degreeTree62_885All`, `OAI.UniversalTensorSquare.degreeTree62_889All`, `OAI.UniversalTensorSquare.degreeTree62_923All`, `OAI.UniversalTensorSquare.degreeTree62_942All`, `OAI.UniversalTensorSquare.degreeTree62_943All`, `OAI.UniversalTensorSquare.degreeTree62_946All`, `OAI.UniversalTensorSquare.degreeTree62_947All`, `OAI.UniversalTensorSquare.degreeTree62_950All`, `OAI.UniversalTensorSquare.degreeTree62_953All`, `OAI.UniversalTensorSquare.degreeTree62_955All`, `OAI.UniversalTensorSquare.degreeTree62_968All`, `OAI.UniversalTensorSquare.sg33843`, `OAI.UniversalTensorSquare.sg33859`, `OAI.UniversalTensorSquare.sg34122`, `OAI.UniversalTensorSquare.sg34170`, `OAI.UniversalTensorSquare.sg34179`, `OAI.UniversalTensorSquare.sg34329`, `OAI.UniversalTensorSquare.sg34364`, `OAI.UniversalTensorSquare.sg34395`, `OAI.UniversalTensorSquare.sg34510`, `OAI.UniversalTensorSquare.sg34535`, `OAI.UniversalTensorSquare.sg36993`, `OAI.UniversalTensorSquare.sg38175`, `OAI.UniversalTensorSquare.sg38186`, `OAI.UniversalTensorSquare.sg38281`, `OAI.UniversalTensorSquare.sg38552`, `OAI.UniversalTensorSquare.sg38688`, `OAI.UniversalTensorSquare.sg38721`, `OAI.UniversalTensorSquare.sg38727`, `OAI.UniversalTensorSquare.sg38849`, `OAI.UniversalTensorSquare.sg38873`, `OAI.UniversalTensorSquare.sg39324`, `OAI.UniversalTensorSquare.sg39615`, `OAI.UniversalTensorSquare.sg39625`, `OAI.UniversalTensorSquare.sg39731`, `OAI.UniversalTensorSquare.sg39736`, `OAI.UniversalTensorSquare.sg39815`, `OAI.UniversalTensorSquare.sg39937`, `OAI.UniversalTensorSquare.sg40205`, `OAI.UniversalTensorSquare.sg41068`, `OAI.UniversalTensorSquare.sg41074`, `OAI.UniversalTensorSquare.sg41155`, `OAI.UniversalTensorSquare.sg41637`, `OAI.UniversalTensorSquare.sg41729`, `OAI.UniversalTensorSquare.sg41734`, `OAI.UniversalTensorSquare.sg41754`, `OAI.UniversalTensorSquare.sg41808`, `OAI.UniversalTensorSquare.sg41824`, `OAI.UniversalTensorSquare.sg41826`, `OAI.UniversalTensorSquare.sg41889`, `OAI.UniversalTensorSquare.sg41894`, `OAI.UniversalTensorSquare.sg41922`, `OAI.UniversalTensorSquare.sg41940`, `OAI.UniversalTensorSquare.sg41956`, `OAI.UniversalTensorSquare.sg41958`, `OAI.UniversalTensorSquare.sg41991`, `OAI.UniversalTensorSquare.sg42004`, `OAI.UniversalTensorSquare.sg42017`, `OAI.UniversalTensorSquare.sg42057`, `OAI.UniversalTensorSquare.sg42059`, `OAI.UniversalTensorSquare.sg42068`, `OAI.UniversalTensorSquare.sg42076`, `OAI.UniversalTensorSquare.sg42148`, `OAI.UniversalTensorSquare.sg42177`, `OAI.UniversalTensorSquare.sg42198`, `OAI.UniversalTensorSquare.sg42239`, `OAI.UniversalTensorSquare.sg42243`, `OAI.UniversalTensorSquare.sg42267`, `OAI.UniversalTensorSquare.sg42282`, `OAI.UniversalTensorSquare.sg42285`, `OAI.UniversalTensorSquare.sg42296`, `OAI.UniversalTensorSquare.sg42298`, `OAI.UniversalTensorSquare.sg42326`, `OAI.UniversalTensorSquare.sg42337`, `OAI.UniversalTensorSquare.sg42339`, `OAI.UniversalTensorSquare.sg42349`, `OAI.UniversalTensorSquare.sg42390`, `OAI.UniversalTensorSquare.sg42408`, `OAI.UniversalTensorSquare.sg42432`, `OAI.UniversalTensorSquare.sg42484`, `OAI.UniversalTensorSquare.sg42499`, `OAI.UniversalTensorSquare.sg42530`, `OAI.UniversalTensorSquare.sg42536`, `OAI.UniversalTensorSquare.sg42567`, `OAI.UniversalTensorSquare.sg42589`, `OAI.UniversalTensorSquare.sg42593`, `OAI.UniversalTensorSquare.sg42612`, `OAI.UniversalTensorSquare.sg42625`, `OAI.UniversalTensorSquare.sg42628`, `OAI.UniversalTensorSquare.sg42638`, `OAI.UniversalTensorSquare.sg42640`, `OAI.UniversalTensorSquare.sg42661`, `OAI.UniversalTensorSquare.sg42675`, `OAI.UniversalTensorSquare.sg42687`, `OAI.UniversalTensorSquare.sg42691`, `OAI.UniversalTensorSquare.sg42706`, `OAI.UniversalTensorSquare.sg42720`, `OAI.UniversalTensorSquare.sg42721`, `OAI.UniversalTensorSquare.sg42729`, `OAI.UniversalTensorSquare.sg42733`, `OAI.UniversalTensorSquare.sg42736`, `OAI.UniversalTensorSquare.sg42750`, `OAI.UniversalTensorSquare.sg42754`, `OAI.UniversalTensorSquare.sg42763`, `OAI.UniversalTensorSquare.sg42765` and `OAI.UniversalTensorSquare.sg42921` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes47.lean (declaration OAI.UniversalTensorSquare.sg19623)

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

lemma sg19623 : RowSquare [8,6,4,3,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,3,2,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
