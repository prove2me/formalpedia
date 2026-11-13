-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg516
-- name    : OAI.UniversalTensorSquare.sg516
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:19:33.908448+00:00
-- url     : https://prove2.me/theorems/ac054f0c-b9c6-4f8f-9c4f-2796cd1ca7d9
-- title:
--   OAI.UniversalTensorSquare.sg516: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg516` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg516 : RowSquare [3,3,3] [1,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_1004All`, `OAI.UniversalTensorSquare.degreeTree62_311All`, `OAI.UniversalTensorSquare.degreeTree62_318All`, `OAI.UniversalTensorSquare.degreeTree62_323All`, `OAI.UniversalTensorSquare.degreeTree62_329All`, `OAI.UniversalTensorSquare.degreeTree62_332All`, `OAI.UniversalTensorSquare.degreeTree62_339All`, `OAI.UniversalTensorSquare.degreeTree62_340All`, `OAI.UniversalTensorSquare.degreeTree62_436All`, `OAI.UniversalTensorSquare.degreeTree62_437All`, `OAI.UniversalTensorSquare.degreeTree62_519All`, `OAI.UniversalTensorSquare.degreeTree62_562All`, `OAI.UniversalTensorSquare.degreeTree62_630All`, `OAI.UniversalTensorSquare.degreeTree62_743All`, `OAI.UniversalTensorSquare.degreeTree62_749All`, `OAI.UniversalTensorSquare.degreeTree62_752All`, `OAI.UniversalTensorSquare.degreeTree62_758All`, `OAI.UniversalTensorSquare.degreeTree62_778All`, `OAI.UniversalTensorSquare.degreeTree62_790All`, `OAI.UniversalTensorSquare.degreeTree62_802All`, `OAI.UniversalTensorSquare.degreeTree62_847All`, `OAI.UniversalTensorSquare.degreeTree62_909All`, `OAI.UniversalTensorSquare.degreeTree62_934All`, `OAI.UniversalTensorSquare.degreeTree62_990All`, `OAI.UniversalTensorSquare.sg12468`, `OAI.UniversalTensorSquare.sg18387`, `OAI.UniversalTensorSquare.sg18421`, `OAI.UniversalTensorSquare.sg18500`, `OAI.UniversalTensorSquare.sg18669`, `OAI.UniversalTensorSquare.sg18717`, `OAI.UniversalTensorSquare.sg18783`, `OAI.UniversalTensorSquare.sg18787`, `OAI.UniversalTensorSquare.sg2213`, `OAI.UniversalTensorSquare.sg2335`, `OAI.UniversalTensorSquare.sg32086`, `OAI.UniversalTensorSquare.sg33208`, `OAI.UniversalTensorSquare.sg33209`, `OAI.UniversalTensorSquare.sg33210`, `OAI.UniversalTensorSquare.sg34618`, `OAI.UniversalTensorSquare.sg34621`, `OAI.UniversalTensorSquare.sg34623`, `OAI.UniversalTensorSquare.sg35117`, `OAI.UniversalTensorSquare.sg35118`, `OAI.UniversalTensorSquare.sg35119`, `OAI.UniversalTensorSquare.sg35143`, `OAI.UniversalTensorSquare.sg35473`, `OAI.UniversalTensorSquare.sg35487`, `OAI.UniversalTensorSquare.sg35489`, `OAI.UniversalTensorSquare.sg35498`, `OAI.UniversalTensorSquare.sg35502`, `OAI.UniversalTensorSquare.sg35504`, `OAI.UniversalTensorSquare.sg35513`, `OAI.UniversalTensorSquare.sg35523`, `OAI.UniversalTensorSquare.sg35527`, `OAI.UniversalTensorSquare.sg35529`, `OAI.UniversalTensorSquare.sg35537`, `OAI.UniversalTensorSquare.sg35554`, `OAI.UniversalTensorSquare.sg35567`, `OAI.UniversalTensorSquare.sg35569`, `OAI.UniversalTensorSquare.sg35571`, `OAI.UniversalTensorSquare.sg35597`, `OAI.UniversalTensorSquare.sg35599`, `OAI.UniversalTensorSquare.sg35601`, `OAI.UniversalTensorSquare.sg35678`, `OAI.UniversalTensorSquare.sg35686`, `OAI.UniversalTensorSquare.sg35690`, `OAI.UniversalTensorSquare.sg35692`, `OAI.UniversalTensorSquare.sg35773`, `OAI.UniversalTensorSquare.sg35775`, `OAI.UniversalTensorSquare.sg35777`, `OAI.UniversalTensorSquare.sg35819`, `OAI.UniversalTensorSquare.sg35821`, `OAI.UniversalTensorSquare.sg35823`, `OAI.UniversalTensorSquare.sg35932`, `OAI.UniversalTensorSquare.sg35934`, `OAI.UniversalTensorSquare.sg35936`, `OAI.UniversalTensorSquare.sg35982`, `OAI.UniversalTensorSquare.sg35984`, `OAI.UniversalTensorSquare.sg35986`, `OAI.UniversalTensorSquare.sg36364`, `OAI.UniversalTensorSquare.sg36366`, `OAI.UniversalTensorSquare.sg36368`, `OAI.UniversalTensorSquare.sg36491`, `OAI.UniversalTensorSquare.sg36493`, `OAI.UniversalTensorSquare.sg36495`, `OAI.UniversalTensorSquare.sg36539`, `OAI.UniversalTensorSquare.sg36541`, `OAI.UniversalTensorSquare.sg36543`, `OAI.UniversalTensorSquare.sg36852`, `OAI.UniversalTensorSquare.sg37716`, `OAI.UniversalTensorSquare.sg37717`, `OAI.UniversalTensorSquare.sg37738`, `OAI.UniversalTensorSquare.sg37742`, `OAI.UniversalTensorSquare.sg38921`, `OAI.UniversalTensorSquare.sg38923`, `OAI.UniversalTensorSquare.sg38925`, `OAI.UniversalTensorSquare.sg38926`, `OAI.UniversalTensorSquare.sg39535`, `OAI.UniversalTensorSquare.sg39537`, `OAI.UniversalTensorSquare.sg39538`, `OAI.UniversalTensorSquare.sg39995`, `OAI.UniversalTensorSquare.sg40052`, `OAI.UniversalTensorSquare.sg40233`, `OAI.UniversalTensorSquare.sg40239`, `OAI.UniversalTensorSquare.sg40242`, `OAI.UniversalTensorSquare.sg40243`, `OAI.UniversalTensorSquare.sg40247`, `OAI.UniversalTensorSquare.sg40254`, `OAI.UniversalTensorSquare.sg40257`, `OAI.UniversalTensorSquare.sg40258`, `OAI.UniversalTensorSquare.sg40267`, `OAI.UniversalTensorSquare.sg40305`, `OAI.UniversalTensorSquare.sg40307`, `OAI.UniversalTensorSquare.sg40308`, `OAI.UniversalTensorSquare.sg40330`, `OAI.UniversalTensorSquare.sg40332`, `OAI.UniversalTensorSquare.sg40333`, `OAI.UniversalTensorSquare.sg40372`, `OAI.UniversalTensorSquare.sg40379`, `OAI.UniversalTensorSquare.sg40382`, `OAI.UniversalTensorSquare.sg40383`, `OAI.UniversalTensorSquare.sg40449`, `OAI.UniversalTensorSquare.sg40451`, `OAI.UniversalTensorSquare.sg40452`, `OAI.UniversalTensorSquare.sg40541`, `OAI.UniversalTensorSquare.sg40543`, `OAI.UniversalTensorSquare.sg40544`, `OAI.UniversalTensorSquare.sg40785`, `OAI.UniversalTensorSquare.sg40807`, `OAI.UniversalTensorSquare.sg40809`, `OAI.UniversalTensorSquare.sg40810`, `OAI.UniversalTensorSquare.sg40840`, `OAI.UniversalTensorSquare.sg40842`, `OAI.UniversalTensorSquare.sg40851`, `OAI.UniversalTensorSquare.sg40974`, `OAI.UniversalTensorSquare.sg41138`, `OAI.UniversalTensorSquare.sg41200`, `OAI.UniversalTensorSquare.sg41217`, `OAI.UniversalTensorSquare.sg41424`, `OAI.UniversalTensorSquare.sg41549`, `OAI.UniversalTensorSquare.sg41795`, `OAI.UniversalTensorSquare.sg41872`, `OAI.UniversalTensorSquare.sg42513`, `OAI.UniversalTensorSquare.sg42693`, `OAI.UniversalTensorSquare.sg42709`, `OAI.UniversalTensorSquare.sg42925`, `OAI.UniversalTensorSquare.sg42942`, `OAI.UniversalTensorSquare.sg42951`, `OAI.UniversalTensorSquare.sg43047`, `OAI.UniversalTensorSquare.sg43059`, `OAI.UniversalTensorSquare.sg43091`, `OAI.UniversalTensorSquare.sg43148` and `OAI.UniversalTensorSquare.sg798` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg516)

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

lemma sg516 : RowSquare [3,3,3] [1,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
