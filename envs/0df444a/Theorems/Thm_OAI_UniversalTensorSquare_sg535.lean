-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg535
-- name    : OAI.UniversalTensorSquare.sg535
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T22:40:54.606553+00:00
-- url     : https://prove2.me/theorems/d8b24229-00f6-4bf4-bda1-68c0f5420eba
-- title:
--   OAI.UniversalTensorSquare.sg535: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg535` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg535 : RowSquare [4,2,1,1,1] [2,2,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_100All`, `OAI.UniversalTensorSquare.degreeTree39_110All`, `OAI.UniversalTensorSquare.degreeTree39_19All`, `OAI.UniversalTensorSquare.degreeTree43_101All`, `OAI.UniversalTensorSquare.degreeTree43_205All`, `OAI.UniversalTensorSquare.degreeTree43_224All`, `OAI.UniversalTensorSquare.degreeTree43_234All`, `OAI.UniversalTensorSquare.degreeTree43_236All`, `OAI.UniversalTensorSquare.degreeTree43_242All`, `OAI.UniversalTensorSquare.degreeTree43_280All`, `OAI.UniversalTensorSquare.degreeTree43_285All`, `OAI.UniversalTensorSquare.degreeTree43_292All`, `OAI.UniversalTensorSquare.degreeTree43_298All`, `OAI.UniversalTensorSquare.degreeTree43_299All`, `OAI.UniversalTensorSquare.degreeTree43_321All`, `OAI.UniversalTensorSquare.degreeTree43_385All`, `OAI.UniversalTensorSquare.degreeTree43_446All`, `OAI.UniversalTensorSquare.degreeTree43_473All`, `OAI.UniversalTensorSquare.degreeTree43_532All`, `OAI.UniversalTensorSquare.degreeTree43_565All`, `OAI.UniversalTensorSquare.degreeTree43_580All`, `OAI.UniversalTensorSquare.degreeTree43_585All`, `OAI.UniversalTensorSquare.degreeTree43_593All`, `OAI.UniversalTensorSquare.degreeTree43_595All`, `OAI.UniversalTensorSquare.degreeTree43_598All`, `OAI.UniversalTensorSquare.degreeTree43_601All`, `OAI.UniversalTensorSquare.degreeTree43_609All`, `OAI.UniversalTensorSquare.degreeTree43_615All`, `OAI.UniversalTensorSquare.degreeTree43_616All`, `OAI.UniversalTensorSquare.degreeTree43_619All`, `OAI.UniversalTensorSquare.degreeTree43_625All`, `OAI.UniversalTensorSquare.degreeTree43_645All`, `OAI.UniversalTensorSquare.degreeTree43_92All`, `OAI.UniversalTensorSquare.degreeTree62_213All`, `OAI.UniversalTensorSquare.degreeTree62_529All`, `OAI.UniversalTensorSquare.degreeTree62_530All`, `OAI.UniversalTensorSquare.degreeTree62_627All`, `OAI.UniversalTensorSquare.degreeTree62_631All`, `OAI.UniversalTensorSquare.degreeTree62_727All`, `OAI.UniversalTensorSquare.degreeTree62_738All`, `OAI.UniversalTensorSquare.degreeTree62_956All`, `OAI.UniversalTensorSquare.sg21909`, `OAI.UniversalTensorSquare.sg21918`, `OAI.UniversalTensorSquare.sg21930`, `OAI.UniversalTensorSquare.sg21942`, `OAI.UniversalTensorSquare.sg21994`, `OAI.UniversalTensorSquare.sg22011`, `OAI.UniversalTensorSquare.sg22342`, `OAI.UniversalTensorSquare.sg22351`, `OAI.UniversalTensorSquare.sg22652`, `OAI.UniversalTensorSquare.sg22691`, `OAI.UniversalTensorSquare.sg22929`, `OAI.UniversalTensorSquare.sg22966`, `OAI.UniversalTensorSquare.sg23130`, `OAI.UniversalTensorSquare.sg23639`, `OAI.UniversalTensorSquare.sg24502`, `OAI.UniversalTensorSquare.sg24522`, `OAI.UniversalTensorSquare.sg24545`, `OAI.UniversalTensorSquare.sg24551`, `OAI.UniversalTensorSquare.sg24562`, `OAI.UniversalTensorSquare.sg24596`, `OAI.UniversalTensorSquare.sg24627`, `OAI.UniversalTensorSquare.sg24636`, `OAI.UniversalTensorSquare.sg24708`, `OAI.UniversalTensorSquare.sg24712`, `OAI.UniversalTensorSquare.sg24738`, `OAI.UniversalTensorSquare.sg24836`, `OAI.UniversalTensorSquare.sg24878`, `OAI.UniversalTensorSquare.sg24914`, `OAI.UniversalTensorSquare.sg25871`, `OAI.UniversalTensorSquare.sg25891`, `OAI.UniversalTensorSquare.sg26581`, `OAI.UniversalTensorSquare.sg26609`, `OAI.UniversalTensorSquare.sg26618`, `OAI.UniversalTensorSquare.sg26640`, `OAI.UniversalTensorSquare.sg26695`, `OAI.UniversalTensorSquare.sg27127`, `OAI.UniversalTensorSquare.sg27205`, `OAI.UniversalTensorSquare.sg27265`, `OAI.UniversalTensorSquare.sg27292`, `OAI.UniversalTensorSquare.sg27302`, `OAI.UniversalTensorSquare.sg27348`, `OAI.UniversalTensorSquare.sg27375`, `OAI.UniversalTensorSquare.sg27405`, `OAI.UniversalTensorSquare.sg27457`, `OAI.UniversalTensorSquare.sg27552`, `OAI.UniversalTensorSquare.sg27557`, `OAI.UniversalTensorSquare.sg30794`, `OAI.UniversalTensorSquare.sg31199`, `OAI.UniversalTensorSquare.sg31333`, `OAI.UniversalTensorSquare.sg31584`, `OAI.UniversalTensorSquare.sg31614`, `OAI.UniversalTensorSquare.sg33661`, `OAI.UniversalTensorSquare.sg34061`, `OAI.UniversalTensorSquare.sg34262`, `OAI.UniversalTensorSquare.sg34263`, `OAI.UniversalTensorSquare.sg34450`, `OAI.UniversalTensorSquare.sg35793`, `OAI.UniversalTensorSquare.sg36450`, `OAI.UniversalTensorSquare.sg36588`, `OAI.UniversalTensorSquare.sg36659`, `OAI.UniversalTensorSquare.sg37887`, `OAI.UniversalTensorSquare.sg38006`, `OAI.UniversalTensorSquare.sg40094`, `OAI.UniversalTensorSquare.sg40813`, `OAI.UniversalTensorSquare.sg42109`, `OAI.UniversalTensorSquare.sg42612`, `OAI.UniversalTensorSquare.sg42705`, `OAI.UniversalTensorSquare.sg42721`, `OAI.UniversalTensorSquare.sg4988` and `OAI.UniversalTensorSquare.sg7781` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean (declaration OAI.UniversalTensorSquare.sg535)

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

lemma sg535 : RowSquare [4,2,1,1,1] [2,2,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
