-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg997
-- name    : OAI.UniversalTensorSquare.sg997
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T00:11:01.441117+00:00
-- url     : https://prove2.me/theorems/2d46565b-aa6e-4228-948a-6c4683b6090f
-- title:
--   OAI.UniversalTensorSquare.sg997: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg997` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg997 : RowSquare [6,1,1,1,1] [2,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_77All`, `OAI.UniversalTensorSquare.degreeTree43_185All`, `OAI.UniversalTensorSquare.degreeTree43_228All`, `OAI.UniversalTensorSquare.degreeTree43_234All`, `OAI.UniversalTensorSquare.degreeTree43_368All`, `OAI.UniversalTensorSquare.degreeTree43_385All`, `OAI.UniversalTensorSquare.degreeTree43_389All`, `OAI.UniversalTensorSquare.degreeTree43_411All`, `OAI.UniversalTensorSquare.degreeTree43_421All`, `OAI.UniversalTensorSquare.degreeTree43_432All`, `OAI.UniversalTensorSquare.degreeTree43_445All`, `OAI.UniversalTensorSquare.degreeTree43_446All`, `OAI.UniversalTensorSquare.degreeTree43_47All`, `OAI.UniversalTensorSquare.degreeTree43_57All`, `OAI.UniversalTensorSquare.degreeTree62_464All`, `OAI.UniversalTensorSquare.degreeTree62_809All`, `OAI.UniversalTensorSquare.degreeTree62_833All`, `OAI.UniversalTensorSquare.degreeTree62_871All`, `OAI.UniversalTensorSquare.degreeTree62_893All`, `OAI.UniversalTensorSquare.degreeTreeAll39`, `OAI.UniversalTensorSquare.sg18746`, `OAI.UniversalTensorSquare.sg21798`, `OAI.UniversalTensorSquare.sg22535`, `OAI.UniversalTensorSquare.sg22705`, `OAI.UniversalTensorSquare.sg22734`, `OAI.UniversalTensorSquare.sg22807`, `OAI.UniversalTensorSquare.sg22979`, `OAI.UniversalTensorSquare.sg23061`, `OAI.UniversalTensorSquare.sg23340`, `OAI.UniversalTensorSquare.sg23756`, `OAI.UniversalTensorSquare.sg23829`, `OAI.UniversalTensorSquare.sg23896`, `OAI.UniversalTensorSquare.sg23977`, `OAI.UniversalTensorSquare.sg24001`, `OAI.UniversalTensorSquare.sg24031`, `OAI.UniversalTensorSquare.sg24143`, `OAI.UniversalTensorSquare.sg24247`, `OAI.UniversalTensorSquare.sg24427`, `OAI.UniversalTensorSquare.sg25415`, `OAI.UniversalTensorSquare.sg25430`, `OAI.UniversalTensorSquare.sg25514`, `OAI.UniversalTensorSquare.sg25582`, `OAI.UniversalTensorSquare.sg26224`, `OAI.UniversalTensorSquare.sg28411`, `OAI.UniversalTensorSquare.sg28575`, `OAI.UniversalTensorSquare.sg28601`, `OAI.UniversalTensorSquare.sg28776`, `OAI.UniversalTensorSquare.sg29292`, `OAI.UniversalTensorSquare.sg29315`, `OAI.UniversalTensorSquare.sg29417`, `OAI.UniversalTensorSquare.sg29462`, `OAI.UniversalTensorSquare.sg30820`, `OAI.UniversalTensorSquare.sg30887`, `OAI.UniversalTensorSquare.sg33033`, `OAI.UniversalTensorSquare.sg35484`, `OAI.UniversalTensorSquare.sg35486`, `OAI.UniversalTensorSquare.sg36707`, `OAI.UniversalTensorSquare.sg37166`, `OAI.UniversalTensorSquare.sg37168`, `OAI.UniversalTensorSquare.sg37317`, `OAI.UniversalTensorSquare.sg37321`, `OAI.UniversalTensorSquare.sg37653`, `OAI.UniversalTensorSquare.sg37682`, `OAI.UniversalTensorSquare.sg37704`, `OAI.UniversalTensorSquare.sg38064`, `OAI.UniversalTensorSquare.sg38068`, `OAI.UniversalTensorSquare.sg39059`, `OAI.UniversalTensorSquare.sg39061`, `OAI.UniversalTensorSquare.sg39063`, `OAI.UniversalTensorSquare.sg40570`, `OAI.UniversalTensorSquare.sg40572`, `OAI.UniversalTensorSquare.sg40573`, `OAI.UniversalTensorSquare.sg40657`, `OAI.UniversalTensorSquare.sg40659`, `OAI.UniversalTensorSquare.sg40660`, `OAI.UniversalTensorSquare.sg40870`, `OAI.UniversalTensorSquare.sg40951`, `OAI.UniversalTensorSquare.sg40998`, `OAI.UniversalTensorSquare.sg41001`, `OAI.UniversalTensorSquare.sg41244`, `OAI.UniversalTensorSquare.sg41246`, `OAI.UniversalTensorSquare.sg41247`, `OAI.UniversalTensorSquare.sg41661`, `OAI.UniversalTensorSquare.sg6906` and `OAI.UniversalTensorSquare.sg6907` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes1.lean (declaration OAI.UniversalTensorSquare.sg997)

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

lemma sg997 : RowSquare [6,1,1,1,1] [2,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
