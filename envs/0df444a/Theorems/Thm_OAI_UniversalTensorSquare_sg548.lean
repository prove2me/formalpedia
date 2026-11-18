-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg548
-- name    : OAI.UniversalTensorSquare.sg548
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T22:43:54.346922+00:00
-- url     : https://prove2.me/theorems/f39a7dcd-3f95-4d2b-8086-4846de95c458
-- title:
--   OAI.UniversalTensorSquare.sg548: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg548` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg548 : RowSquare [4,2,2,1] [2,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_427All`, `OAI.UniversalTensorSquare.degreeTree62_547All`, `OAI.UniversalTensorSquare.degreeTree62_796All`, `OAI.UniversalTensorSquare.sg12216`, `OAI.UniversalTensorSquare.sg12236`, `OAI.UniversalTensorSquare.sg12238`, `OAI.UniversalTensorSquare.sg13238`, `OAI.UniversalTensorSquare.sg21686`, `OAI.UniversalTensorSquare.sg27659`, `OAI.UniversalTensorSquare.sg27890`, `OAI.UniversalTensorSquare.sg35484`, `OAI.UniversalTensorSquare.sg35486`, `OAI.UniversalTensorSquare.sg35526`, `OAI.UniversalTensorSquare.sg35540`, `OAI.UniversalTensorSquare.sg35542`, `OAI.UniversalTensorSquare.sg35610`, `OAI.UniversalTensorSquare.sg35723`, `OAI.UniversalTensorSquare.sg35933`, `OAI.UniversalTensorSquare.sg35983`, `OAI.UniversalTensorSquare.sg36032`, `OAI.UniversalTensorSquare.sg36123`, `OAI.UniversalTensorSquare.sg36142`, `OAI.UniversalTensorSquare.sg36419`, `OAI.UniversalTensorSquare.sg36540`, `OAI.UniversalTensorSquare.sg36723`, `OAI.UniversalTensorSquare.sg36856`, `OAI.UniversalTensorSquare.sg37093`, `OAI.UniversalTensorSquare.sg37112`, `OAI.UniversalTensorSquare.sg37120`, `OAI.UniversalTensorSquare.sg37123`, `OAI.UniversalTensorSquare.sg37125`, `OAI.UniversalTensorSquare.sg37175`, `OAI.UniversalTensorSquare.sg37178`, `OAI.UniversalTensorSquare.sg37180`, `OAI.UniversalTensorSquare.sg37196`, `OAI.UniversalTensorSquare.sg37199`, `OAI.UniversalTensorSquare.sg37201`, `OAI.UniversalTensorSquare.sg37318`, `OAI.UniversalTensorSquare.sg37331`, `OAI.UniversalTensorSquare.sg37523`, `OAI.UniversalTensorSquare.sg38405`, `OAI.UniversalTensorSquare.sg40276`, `OAI.UniversalTensorSquare.sg40313`, `OAI.UniversalTensorSquare.sg40321`, `OAI.UniversalTensorSquare.sg40331`, `OAI.UniversalTensorSquare.sg40422`, `OAI.UniversalTensorSquare.sg40450`, `OAI.UniversalTensorSquare.sg40476`, `OAI.UniversalTensorSquare.sg40525`, `OAI.UniversalTensorSquare.sg40542`, `OAI.UniversalTensorSquare.sg40554`, `OAI.UniversalTensorSquare.sg40556`, `OAI.UniversalTensorSquare.sg40557`, `OAI.UniversalTensorSquare.sg40571`, `OAI.UniversalTensorSquare.sg40582`, `OAI.UniversalTensorSquare.sg40588`, `OAI.UniversalTensorSquare.sg40590`, `OAI.UniversalTensorSquare.sg40591`, `OAI.UniversalTensorSquare.sg40658`, `OAI.UniversalTensorSquare.sg40664`, `OAI.UniversalTensorSquare.sg40666`, `OAI.UniversalTensorSquare.sg40667`, `OAI.UniversalTensorSquare.sg40676`, `OAI.UniversalTensorSquare.sg40678`, `OAI.UniversalTensorSquare.sg40679`, `OAI.UniversalTensorSquare.sg40808`, `OAI.UniversalTensorSquare.sg40824`, `OAI.UniversalTensorSquare.sg40841`, `OAI.UniversalTensorSquare.sg40879`, `OAI.UniversalTensorSquare.sg40959`, `OAI.UniversalTensorSquare.sg40970`, `OAI.UniversalTensorSquare.sg40999`, `OAI.UniversalTensorSquare.sg41082`, `OAI.UniversalTensorSquare.sg41191`, `OAI.UniversalTensorSquare.sg41203`, `OAI.UniversalTensorSquare.sg41209`, `OAI.UniversalTensorSquare.sg41211`, `OAI.UniversalTensorSquare.sg41212`, `OAI.UniversalTensorSquare.sg41245`, `OAI.UniversalTensorSquare.sg41251`, `OAI.UniversalTensorSquare.sg41253`, `OAI.UniversalTensorSquare.sg41254`, `OAI.UniversalTensorSquare.sg41326`, `OAI.UniversalTensorSquare.sg41330`, `OAI.UniversalTensorSquare.sg41331`, `OAI.UniversalTensorSquare.sg41524`, `OAI.UniversalTensorSquare.sg41552`, `OAI.UniversalTensorSquare.sg41560`, `OAI.UniversalTensorSquare.sg41652`, `OAI.UniversalTensorSquare.sg41662`, `OAI.UniversalTensorSquare.sg41849`, `OAI.UniversalTensorSquare.sg41859`, `OAI.UniversalTensorSquare.sg42106`, `OAI.UniversalTensorSquare.sg42127`, `OAI.UniversalTensorSquare.sg42209`, `OAI.UniversalTensorSquare.sg42216`, `OAI.UniversalTensorSquare.sg4926`, `OAI.UniversalTensorSquare.sg7974` and `OAI.UniversalTensorSquare.sg7980` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean (declaration OAI.UniversalTensorSquare.sg548)

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

lemma sg548 : RowSquare [4,2,2,1] [2,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
