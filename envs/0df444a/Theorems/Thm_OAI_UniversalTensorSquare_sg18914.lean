-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg18914
-- name    : OAI.UniversalTensorSquare.sg18914
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T09:11:16.945748+00:00
-- url     : https://prove2.me/theorems/22f2cd95-4608-4530-887c-838f3535caf9
-- title:
--   OAI.UniversalTensorSquare.sg18914: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg18914` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes45.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes45.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg18914 : RowSquare [7,6,4,3,2,2,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,3,2,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_320All`, `OAI.UniversalTensorSquare.degreeTree62_332All`, `OAI.UniversalTensorSquare.degreeTree62_456All`, `OAI.UniversalTensorSquare.degreeTree62_462All`, `OAI.UniversalTensorSquare.degreeTree62_519All`, `OAI.UniversalTensorSquare.degreeTree62_542All`, `OAI.UniversalTensorSquare.degreeTree62_578All`, `OAI.UniversalTensorSquare.sg33880`, `OAI.UniversalTensorSquare.sg34032`, `OAI.UniversalTensorSquare.sg34297`, `OAI.UniversalTensorSquare.sg34318`, `OAI.UniversalTensorSquare.sg34624`, `OAI.UniversalTensorSquare.sg34635`, `OAI.UniversalTensorSquare.sg34647`, `OAI.UniversalTensorSquare.sg34672`, `OAI.UniversalTensorSquare.sg34690`, `OAI.UniversalTensorSquare.sg34704`, `OAI.UniversalTensorSquare.sg34737`, `OAI.UniversalTensorSquare.sg35481`, `OAI.UniversalTensorSquare.sg35497`, `OAI.UniversalTensorSquare.sg35505`, `OAI.UniversalTensorSquare.sg35521`, `OAI.UniversalTensorSquare.sg35530`, `OAI.UniversalTensorSquare.sg35538`, `OAI.UniversalTensorSquare.sg35561`, `OAI.UniversalTensorSquare.sg35576`, `OAI.UniversalTensorSquare.sg35585`, `OAI.UniversalTensorSquare.sg35606`, `OAI.UniversalTensorSquare.sg35614`, `OAI.UniversalTensorSquare.sg35622`, `OAI.UniversalTensorSquare.sg35632`, `OAI.UniversalTensorSquare.sg35693`, `OAI.UniversalTensorSquare.sg35718`, `OAI.UniversalTensorSquare.sg35727`, `OAI.UniversalTensorSquare.sg35742`, `OAI.UniversalTensorSquare.sg35766`, `OAI.UniversalTensorSquare.sg35790`, `OAI.UniversalTensorSquare.sg35808`, `OAI.UniversalTensorSquare.sg35824`, `OAI.UniversalTensorSquare.sg35832`, `OAI.UniversalTensorSquare.sg35846`, `OAI.UniversalTensorSquare.sg35904`, `OAI.UniversalTensorSquare.sg35925`, `OAI.UniversalTensorSquare.sg35929`, `OAI.UniversalTensorSquare.sg35937`, `OAI.UniversalTensorSquare.sg35972`, `OAI.UniversalTensorSquare.sg35976`, `OAI.UniversalTensorSquare.sg35987`, `OAI.UniversalTensorSquare.sg35995`, `OAI.UniversalTensorSquare.sg36016`, `OAI.UniversalTensorSquare.sg36036`, `OAI.UniversalTensorSquare.sg36046`, `OAI.UniversalTensorSquare.sg36053`, `OAI.UniversalTensorSquare.sg36127`, `OAI.UniversalTensorSquare.sg36135`, `OAI.UniversalTensorSquare.sg36146`, `OAI.UniversalTensorSquare.sg36179`, `OAI.UniversalTensorSquare.sg36206`, `OAI.UniversalTensorSquare.sg36218`, `OAI.UniversalTensorSquare.sg36293`, `OAI.UniversalTensorSquare.sg36369`, `OAI.UniversalTensorSquare.sg36378`, `OAI.UniversalTensorSquare.sg36389`, `OAI.UniversalTensorSquare.sg36393`, `OAI.UniversalTensorSquare.sg36414`, `OAI.UniversalTensorSquare.sg36435`, `OAI.UniversalTensorSquare.sg36439`, `OAI.UniversalTensorSquare.sg36447`, `OAI.UniversalTensorSquare.sg36481`, `OAI.UniversalTensorSquare.sg36485`, `OAI.UniversalTensorSquare.sg36496`, `OAI.UniversalTensorSquare.sg36504`, `OAI.UniversalTensorSquare.sg36518`, `OAI.UniversalTensorSquare.sg36525`, `OAI.UniversalTensorSquare.sg36544`, `OAI.UniversalTensorSquare.sg36554`, `OAI.UniversalTensorSquare.sg36561`, `OAI.UniversalTensorSquare.sg36629`, `OAI.UniversalTensorSquare.sg36641`, `OAI.UniversalTensorSquare.sg36645`, `OAI.UniversalTensorSquare.sg36656`, `OAI.UniversalTensorSquare.sg36664`, `OAI.UniversalTensorSquare.sg36685`, `OAI.UniversalTensorSquare.sg36708`, `OAI.UniversalTensorSquare.sg36737`, `OAI.UniversalTensorSquare.sg36760`, `OAI.UniversalTensorSquare.sg36785`, `OAI.UniversalTensorSquare.sg36797`, `OAI.UniversalTensorSquare.sg36877`, `OAI.UniversalTensorSquare.sg36924`, `OAI.UniversalTensorSquare.sg36956`, `OAI.UniversalTensorSquare.sg37027`, `OAI.UniversalTensorSquare.sg37097`, `OAI.UniversalTensorSquare.sg37126`, `OAI.UniversalTensorSquare.sg37133`, `OAI.UniversalTensorSquare.sg37148`, `OAI.UniversalTensorSquare.sg37171`, `OAI.UniversalTensorSquare.sg37181`, `OAI.UniversalTensorSquare.sg37188`, `OAI.UniversalTensorSquare.sg37202`, `OAI.UniversalTensorSquare.sg37214`, `OAI.UniversalTensorSquare.sg37233`, `OAI.UniversalTensorSquare.sg37264`, `OAI.UniversalTensorSquare.sg37278`, `OAI.UniversalTensorSquare.sg37322`, `OAI.UniversalTensorSquare.sg37332`, `OAI.UniversalTensorSquare.sg37369`, `OAI.UniversalTensorSquare.sg37382`, `OAI.UniversalTensorSquare.sg37427`, `OAI.UniversalTensorSquare.sg37477`, `OAI.UniversalTensorSquare.sg37555`, `OAI.UniversalTensorSquare.sg37628`, `OAI.UniversalTensorSquare.sg37723`, `OAI.UniversalTensorSquare.sg37732`, `OAI.UniversalTensorSquare.sg37743`, `OAI.UniversalTensorSquare.sg37754`, `OAI.UniversalTensorSquare.sg37762`, `OAI.UniversalTensorSquare.sg37782`, `OAI.UniversalTensorSquare.sg37793`, `OAI.UniversalTensorSquare.sg37797`, `OAI.UniversalTensorSquare.sg37815`, `OAI.UniversalTensorSquare.sg37827`, `OAI.UniversalTensorSquare.sg37833`, `OAI.UniversalTensorSquare.sg37852`, `OAI.UniversalTensorSquare.sg37860`, `OAI.UniversalTensorSquare.sg37879`, `OAI.UniversalTensorSquare.sg37899`, `OAI.UniversalTensorSquare.sg37920`, `OAI.UniversalTensorSquare.sg37931`, `OAI.UniversalTensorSquare.sg38002`, `OAI.UniversalTensorSquare.sg38010`, `OAI.UniversalTensorSquare.sg38019`, `OAI.UniversalTensorSquare.sg38029`, `OAI.UniversalTensorSquare.sg38035`, `OAI.UniversalTensorSquare.sg38049`, `OAI.UniversalTensorSquare.sg38069`, `OAI.UniversalTensorSquare.sg38079`, `OAI.UniversalTensorSquare.sg38098`, `OAI.UniversalTensorSquare.sg38126`, `OAI.UniversalTensorSquare.sg38155`, `OAI.UniversalTensorSquare.sg38217`, `OAI.UniversalTensorSquare.sg38228`, `OAI.UniversalTensorSquare.sg38251`, `OAI.UniversalTensorSquare.sg38349`, `OAI.UniversalTensorSquare.sg38398`, `OAI.UniversalTensorSquare.sg38409`, `OAI.UniversalTensorSquare.sg38419`, `OAI.UniversalTensorSquare.sg38425`, `OAI.UniversalTensorSquare.sg38437`, `OAI.UniversalTensorSquare.sg38448`, `OAI.UniversalTensorSquare.sg38463`, `OAI.UniversalTensorSquare.sg38481` and `OAI.UniversalTensorSquare.sg38491` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes45.lean (declaration OAI.UniversalTensorSquare.sg18914)

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

lemma sg18914 : RowSquare [7,6,4,3,2,2,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,3,2,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
