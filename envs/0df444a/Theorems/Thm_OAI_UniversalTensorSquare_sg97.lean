-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg97
-- name    : OAI.UniversalTensorSquare.sg97
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-18T00:08:00.561549+00:00
-- url     : https://prove2.me/theorems/07571e00-2b4a-4fee-afa2-47a894340081
-- title:
--   OAI.UniversalTensorSquare.sg97: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg97` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg97 : RowSquare [4,2] [2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_109All`, `OAI.UniversalTensorSquare.degreeTree43_598All`, `OAI.UniversalTensorSquare.degreeTree62_239All`, `OAI.UniversalTensorSquare.degreeTree62_255All`, `OAI.UniversalTensorSquare.degreeTree62_259All`, `OAI.UniversalTensorSquare.degreeTree62_469All`, `OAI.UniversalTensorSquare.degreeTree62_546All`, `OAI.UniversalTensorSquare.degreeTree62_577All`, `OAI.UniversalTensorSquare.degreeTree62_584All`, `OAI.UniversalTensorSquare.degreeTree62_656All`, `OAI.UniversalTensorSquare.degreeTree62_680All`, `OAI.UniversalTensorSquare.degreeTree62_690All`, `OAI.UniversalTensorSquare.degreeTree62_699All`, `OAI.UniversalTensorSquare.degreeTree62_833All`, `OAI.UniversalTensorSquare.degreeTree62_8All`, `OAI.UniversalTensorSquare.degreeTree62_941All`, `OAI.UniversalTensorSquare.sg12043`, `OAI.UniversalTensorSquare.sg17426`, `OAI.UniversalTensorSquare.sg17455`, `OAI.UniversalTensorSquare.sg17457`, `OAI.UniversalTensorSquare.sg17464`, `OAI.UniversalTensorSquare.sg19015`, `OAI.UniversalTensorSquare.sg19089`, `OAI.UniversalTensorSquare.sg19645`, `OAI.UniversalTensorSquare.sg20846`, `OAI.UniversalTensorSquare.sg22045`, `OAI.UniversalTensorSquare.sg32294`, `OAI.UniversalTensorSquare.sg32303`, `OAI.UniversalTensorSquare.sg32724`, `OAI.UniversalTensorSquare.sg33162`, `OAI.UniversalTensorSquare.sg34627`, `OAI.UniversalTensorSquare.sg34637`, `OAI.UniversalTensorSquare.sg34655`, `OAI.UniversalTensorSquare.sg34677`, `OAI.UniversalTensorSquare.sg34685`, `OAI.UniversalTensorSquare.sg34688`, `OAI.UniversalTensorSquare.sg34690`, `OAI.UniversalTensorSquare.sg34724`, `OAI.UniversalTensorSquare.sg34726`, `OAI.UniversalTensorSquare.sg34744`, `OAI.UniversalTensorSquare.sg34763`, `OAI.UniversalTensorSquare.sg34765`, `OAI.UniversalTensorSquare.sg34785`, `OAI.UniversalTensorSquare.sg34935`, `OAI.UniversalTensorSquare.sg35034`, `OAI.UniversalTensorSquare.sg35038`, `OAI.UniversalTensorSquare.sg35040`, `OAI.UniversalTensorSquare.sg35087`, `OAI.UniversalTensorSquare.sg36676`, `OAI.UniversalTensorSquare.sg37095`, `OAI.UniversalTensorSquare.sg37097`, `OAI.UniversalTensorSquare.sg37120`, `OAI.UniversalTensorSquare.sg37123`, `OAI.UniversalTensorSquare.sg37125`, `OAI.UniversalTensorSquare.sg37191`, `OAI.UniversalTensorSquare.sg37196`, `OAI.UniversalTensorSquare.sg37199`, `OAI.UniversalTensorSquare.sg37201`, `OAI.UniversalTensorSquare.sg37510`, `OAI.UniversalTensorSquare.sg38022`, `OAI.UniversalTensorSquare.sg38031`, `OAI.UniversalTensorSquare.sg38033`, `OAI.UniversalTensorSquare.sg38035`, `OAI.UniversalTensorSquare.sg38407`, `OAI.UniversalTensorSquare.sg38409`, `OAI.UniversalTensorSquare.sg38431`, `OAI.UniversalTensorSquare.sg38434`, `OAI.UniversalTensorSquare.sg38436`, `OAI.UniversalTensorSquare.sg38466`, `OAI.UniversalTensorSquare.sg38471`, `OAI.UniversalTensorSquare.sg38487`, `OAI.UniversalTensorSquare.sg39191`, `OAI.UniversalTensorSquare.sg39194`, `OAI.UniversalTensorSquare.sg39196`, `OAI.UniversalTensorSquare.sg39211`, `OAI.UniversalTensorSquare.sg39226`, `OAI.UniversalTensorSquare.sg39231`, `OAI.UniversalTensorSquare.sg39233`, `OAI.UniversalTensorSquare.sg39238`, `OAI.UniversalTensorSquare.sg39240`, `OAI.UniversalTensorSquare.sg39261`, `OAI.UniversalTensorSquare.sg39539`, `OAI.UniversalTensorSquare.sg39549`, `OAI.UniversalTensorSquare.sg39553`, `OAI.UniversalTensorSquare.sg39555`, `OAI.UniversalTensorSquare.sg39556`, `OAI.UniversalTensorSquare.sg39557`, `OAI.UniversalTensorSquare.sg39568`, `OAI.UniversalTensorSquare.sg39570`, `OAI.UniversalTensorSquare.sg39571`, `OAI.UniversalTensorSquare.sg39572`, `OAI.UniversalTensorSquare.sg39588`, `OAI.UniversalTensorSquare.sg39605`, `OAI.UniversalTensorSquare.sg39608`, `OAI.UniversalTensorSquare.sg39609`, `OAI.UniversalTensorSquare.sg39625`, `OAI.UniversalTensorSquare.sg39628`, `OAI.UniversalTensorSquare.sg39684`, `OAI.UniversalTensorSquare.sg39688`, `OAI.UniversalTensorSquare.sg41185`, `OAI.UniversalTensorSquare.sg41190`, `OAI.UniversalTensorSquare.sg41192`, `OAI.UniversalTensorSquare.sg41193`, `OAI.UniversalTensorSquare.sg41544`, `OAI.UniversalTensorSquare.sg41546`, `OAI.UniversalTensorSquare.sg41869`, `OAI.UniversalTensorSquare.sg41882`, `OAI.UniversalTensorSquare.sg41922`, `OAI.UniversalTensorSquare.sg41929`, `OAI.UniversalTensorSquare.sg41938`, `OAI.UniversalTensorSquare.sg41954`, `OAI.UniversalTensorSquare.sg41955`, `OAI.UniversalTensorSquare.sg42233`, `OAI.UniversalTensorSquare.sg42376`, `OAI.UniversalTensorSquare.sg42384`, `OAI.UniversalTensorSquare.sg42388`, `OAI.UniversalTensorSquare.sg42389`, `OAI.UniversalTensorSquare.sg42390`, `OAI.UniversalTensorSquare.sg42396`, `OAI.UniversalTensorSquare.sg42408`, `OAI.UniversalTensorSquare.sg42419`, `OAI.UniversalTensorSquare.sg42430`, `OAI.UniversalTensorSquare.sg42437`, `OAI.UniversalTensorSquare.sg42438`, `OAI.UniversalTensorSquare.sg42439`, `OAI.UniversalTensorSquare.sg42441`, `OAI.UniversalTensorSquare.sg42453`, `OAI.UniversalTensorSquare.sg42701`, `OAI.UniversalTensorSquare.sg43151`, `OAI.UniversalTensorSquare.sg43158`, `OAI.UniversalTensorSquare.sg43169`, `OAI.UniversalTensorSquare.sg4467`, `OAI.UniversalTensorSquare.sg4468`, `OAI.UniversalTensorSquare.sg4871`, `OAI.UniversalTensorSquare.sg5283`, `OAI.UniversalTensorSquare.sg6520`, `OAI.UniversalTensorSquare.sg8035` and `OAI.UniversalTensorSquare.sg8049` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg97)

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

lemma sg97 : RowSquare [4,2] [2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
