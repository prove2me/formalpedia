-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg53
-- name    : OAI.UniversalTensorSquare.sg53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T22:40:53.783877+00:00
-- url     : https://prove2.me/theorems/094cadc5-09ac-4099-b0b2-61311c14b19c
-- title:
--   OAI.UniversalTensorSquare.sg53: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg53` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg53 : RowSquare [2,1,1,1,1] [5,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_507All`, `OAI.UniversalTensorSquare.degreeTree62_975All`, `OAI.UniversalTensorSquare.degreeTreeAll62`, `OAI.UniversalTensorSquare.sg14311`, `OAI.UniversalTensorSquare.sg18363`, `OAI.UniversalTensorSquare.sg19292`, `OAI.UniversalTensorSquare.sg21690`, `OAI.UniversalTensorSquare.sg22787`, `OAI.UniversalTensorSquare.sg25581`, `OAI.UniversalTensorSquare.sg28410`, `OAI.UniversalTensorSquare.sg29060`, `OAI.UniversalTensorSquare.sg32944`, `OAI.UniversalTensorSquare.sg34652`, `OAI.UniversalTensorSquare.sg34707`, `OAI.UniversalTensorSquare.sg34799`, `OAI.UniversalTensorSquare.sg34800`, `OAI.UniversalTensorSquare.sg34801`, `OAI.UniversalTensorSquare.sg34973`, `OAI.UniversalTensorSquare.sg34974`, `OAI.UniversalTensorSquare.sg35139`, `OAI.UniversalTensorSquare.sg35486`, `OAI.UniversalTensorSquare.sg35510`, `OAI.UniversalTensorSquare.sg35542`, `OAI.UniversalTensorSquare.sg35544`, `OAI.UniversalTensorSquare.sg35545`, `OAI.UniversalTensorSquare.sg35546`, `OAI.UniversalTensorSquare.sg35624`, `OAI.UniversalTensorSquare.sg35656`, `OAI.UniversalTensorSquare.sg35669`, `OAI.UniversalTensorSquare.sg35708`, `OAI.UniversalTensorSquare.sg35709`, `OAI.UniversalTensorSquare.sg35783`, `OAI.UniversalTensorSquare.sg35878`, `OAI.UniversalTensorSquare.sg35930`, `OAI.UniversalTensorSquare.sg36018`, `OAI.UniversalTensorSquare.sg36081`, `OAI.UniversalTensorSquare.sg36106`, `OAI.UniversalTensorSquare.sg36138`, `OAI.UniversalTensorSquare.sg36139`, `OAI.UniversalTensorSquare.sg36165`, `OAI.UniversalTensorSquare.sg36249`, `OAI.UniversalTensorSquare.sg36256`, `OAI.UniversalTensorSquare.sg36317`, `OAI.UniversalTensorSquare.sg36344`, `OAI.UniversalTensorSquare.sg36508`, `OAI.UniversalTensorSquare.sg36527`, `OAI.UniversalTensorSquare.sg36719`, `OAI.UniversalTensorSquare.sg36720`, `OAI.UniversalTensorSquare.sg36879`, `OAI.UniversalTensorSquare.sg36880`, `OAI.UniversalTensorSquare.sg36906`, `OAI.UniversalTensorSquare.sg37158`, `OAI.UniversalTensorSquare.sg37191`, `OAI.UniversalTensorSquare.sg37242`, `OAI.UniversalTensorSquare.sg37286`, `OAI.UniversalTensorSquare.sg37346`, `OAI.UniversalTensorSquare.sg37347`, `OAI.UniversalTensorSquare.sg37372`, `OAI.UniversalTensorSquare.sg37390`, `OAI.UniversalTensorSquare.sg37545`, `OAI.UniversalTensorSquare.sg37563`, `OAI.UniversalTensorSquare.sg37601`, `OAI.UniversalTensorSquare.sg37606`, `OAI.UniversalTensorSquare.sg37615`, `OAI.UniversalTensorSquare.sg37645`, `OAI.UniversalTensorSquare.sg37650`, `OAI.UniversalTensorSquare.sg37652`, `OAI.UniversalTensorSquare.sg37656`, `OAI.UniversalTensorSquare.sg37680`, `OAI.UniversalTensorSquare.sg37681`, `OAI.UniversalTensorSquare.sg37707`, `OAI.UniversalTensorSquare.sg37862`, `OAI.UniversalTensorSquare.sg37887`, `OAI.UniversalTensorSquare.sg37901`, `OAI.UniversalTensorSquare.sg38051`, `OAI.UniversalTensorSquare.sg38230`, `OAI.UniversalTensorSquare.sg38916`, `OAI.UniversalTensorSquare.sg39193`, `OAI.UniversalTensorSquare.sg40065`, `OAI.UniversalTensorSquare.sg40293`, `OAI.UniversalTensorSquare.sg40351`, `OAI.UniversalTensorSquare.sg40362`, `OAI.UniversalTensorSquare.sg40366`, `OAI.UniversalTensorSquare.sg40370`, `OAI.UniversalTensorSquare.sg40430`, `OAI.UniversalTensorSquare.sg40575`, `OAI.UniversalTensorSquare.sg40577`, `OAI.UniversalTensorSquare.sg40578`, `OAI.UniversalTensorSquare.sg40651`, `OAI.UniversalTensorSquare.sg40703`, `OAI.UniversalTensorSquare.sg40732`, `OAI.UniversalTensorSquare.sg40780`, `OAI.UniversalTensorSquare.sg41285`, `OAI.UniversalTensorSquare.sg41291`, `OAI.UniversalTensorSquare.sg41314`, `OAI.UniversalTensorSquare.sg41318`, `OAI.UniversalTensorSquare.sg41354`, `OAI.UniversalTensorSquare.sg41376`, `OAI.UniversalTensorSquare.sg41380`, `OAI.UniversalTensorSquare.sg41395`, `OAI.UniversalTensorSquare.sg41398`, `OAI.UniversalTensorSquare.sg41412`, `OAI.UniversalTensorSquare.sg41452`, `OAI.UniversalTensorSquare.sg41467`, `OAI.UniversalTensorSquare.sg41470`, `OAI.UniversalTensorSquare.sg41483`, `OAI.UniversalTensorSquare.sg41485`, `OAI.UniversalTensorSquare.sg42793`, `OAI.UniversalTensorSquare.sg42807`, `OAI.UniversalTensorSquare.sg42814`, `OAI.UniversalTensorSquare.sg42819`, `OAI.UniversalTensorSquare.sg42823`, `OAI.UniversalTensorSquare.sg42832`, `OAI.UniversalTensorSquare.sg42843`, `OAI.UniversalTensorSquare.sg42854`, `OAI.UniversalTensorSquare.sg42857`, `OAI.UniversalTensorSquare.sg4286`, `OAI.UniversalTensorSquare.sg42870`, `OAI.UniversalTensorSquare.sg42908`, `OAI.UniversalTensorSquare.sg42932`, `OAI.UniversalTensorSquare.sg42937`, `OAI.UniversalTensorSquare.sg42952`, `OAI.UniversalTensorSquare.sg42958`, `OAI.UniversalTensorSquare.sg43039`, `OAI.UniversalTensorSquare.sg43133`, `OAI.UniversalTensorSquare.sg4966`, `OAI.UniversalTensorSquare.sg5579`, `OAI.UniversalTensorSquare.sg5605`, `OAI.UniversalTensorSquare.sg587`, `OAI.UniversalTensorSquare.sg6154`, `OAI.UniversalTensorSquare.sg6182`, `OAI.UniversalTensorSquare.sg6186`, `OAI.UniversalTensorSquare.sg6187`, `OAI.UniversalTensorSquare.sg6305`, `OAI.UniversalTensorSquare.sg6309`, `OAI.UniversalTensorSquare.sg6310`, `OAI.UniversalTensorSquare.sg6401`, `OAI.UniversalTensorSquare.sg6768`, `OAI.UniversalTensorSquare.sg6780`, `OAI.UniversalTensorSquare.sg7056`, `OAI.UniversalTensorSquare.sg7069`, `OAI.UniversalTensorSquare.sg7071`, `OAI.UniversalTensorSquare.sg7366`, `OAI.UniversalTensorSquare.sg8178`, `OAI.UniversalTensorSquare.sg8350`, `OAI.UniversalTensorSquare.sg8365`, `OAI.UniversalTensorSquare.sg8986`, `OAI.UniversalTensorSquare.sg9250`, `OAI.UniversalTensorSquare.sg9253`, `OAI.UniversalTensorSquare.sg9256`, `OAI.UniversalTensorSquare.sg9694`, `OAI.UniversalTensorSquare.sg9697` and `OAI.UniversalTensorSquare.sg9798` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean (declaration OAI.UniversalTensorSquare.sg53)

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

lemma sg53 : RowSquare [2,1,1,1,1] [5,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
