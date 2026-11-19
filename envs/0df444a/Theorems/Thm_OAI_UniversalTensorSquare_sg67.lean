-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg67
-- name    : OAI.UniversalTensorSquare.sg67
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T23:01:25.042569+00:00
-- url     : https://prove2.me/theorems/92920472-ac90-43e3-8720-a4643ce487a4
-- title:
--   OAI.UniversalTensorSquare.sg67: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg67` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg67 : RowSquare [3,1,1,1] [2,2,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree26_11All`, `OAI.UniversalTensorSquare.degreeTree26_18All`, `OAI.UniversalTensorSquare.degreeTree26_19All`, `OAI.UniversalTensorSquare.degreeTree26_24All`, `OAI.UniversalTensorSquare.degreeTree26_33All`, `OAI.UniversalTensorSquare.degreeTree62_669All`, `OAI.UniversalTensorSquare.sg22343`, `OAI.UniversalTensorSquare.sg24617`, `OAI.UniversalTensorSquare.sg24761`, `OAI.UniversalTensorSquare.sg24907`, `OAI.UniversalTensorSquare.sg26274`, `OAI.UniversalTensorSquare.sg26550`, `OAI.UniversalTensorSquare.sg27094`, `OAI.UniversalTensorSquare.sg27248`, `OAI.UniversalTensorSquare.sg27262`, `OAI.UniversalTensorSquare.sg27263`, `OAI.UniversalTensorSquare.sg27316`, `OAI.UniversalTensorSquare.sg27330`, `OAI.UniversalTensorSquare.sg27332`, `OAI.UniversalTensorSquare.sg27423`, `OAI.UniversalTensorSquare.sg30295`, `OAI.UniversalTensorSquare.sg30859`, `OAI.UniversalTensorSquare.sg31181`, `OAI.UniversalTensorSquare.sg31183`, `OAI.UniversalTensorSquare.sg32963`, `OAI.UniversalTensorSquare.sg33011`, `OAI.UniversalTensorSquare.sg34288`, `OAI.UniversalTensorSquare.sg35758`, `OAI.UniversalTensorSquare.sg36415`, `OAI.UniversalTensorSquare.sg36471`, `OAI.UniversalTensorSquare.sg36487`, `OAI.UniversalTensorSquare.sg36488`, `OAI.UniversalTensorSquare.sg36489`, `OAI.UniversalTensorSquare.sg36698`, `OAI.UniversalTensorSquare.sg37724`, `OAI.UniversalTensorSquare.sg37783`, `OAI.UniversalTensorSquare.sg37784`, `OAI.UniversalTensorSquare.sg37842`, `OAI.UniversalTensorSquare.sg37843`, `OAI.UniversalTensorSquare.sg37844`, `OAI.UniversalTensorSquare.sg37845`, `OAI.UniversalTensorSquare.sg37848`, `OAI.UniversalTensorSquare.sg37891`, `OAI.UniversalTensorSquare.sg37992`, `OAI.UniversalTensorSquare.sg37998`, `OAI.UniversalTensorSquare.sg38060`, `OAI.UniversalTensorSquare.sg38934`, `OAI.UniversalTensorSquare.sg38997`, `OAI.UniversalTensorSquare.sg38998`, `OAI.UniversalTensorSquare.sg39060`, `OAI.UniversalTensorSquare.sg39198`, `OAI.UniversalTensorSquare.sg39203`, `OAI.UniversalTensorSquare.sg39267`, `OAI.UniversalTensorSquare.sg39415`, `OAI.UniversalTensorSquare.sg39561`, `OAI.UniversalTensorSquare.sg4041`, `OAI.UniversalTensorSquare.sg40863`, `OAI.UniversalTensorSquare.sg40865`, `OAI.UniversalTensorSquare.sg41593`, `OAI.UniversalTensorSquare.sg42097`, `OAI.UniversalTensorSquare.sg42101`, `OAI.UniversalTensorSquare.sg42152`, `OAI.UniversalTensorSquare.sg42162`, `OAI.UniversalTensorSquare.sg42323`, `OAI.UniversalTensorSquare.sg42364`, `OAI.UniversalTensorSquare.sg42515`, `OAI.UniversalTensorSquare.sg4358`, `OAI.UniversalTensorSquare.sg5275`, `OAI.UniversalTensorSquare.sg7344`, `OAI.UniversalTensorSquare.sg7395` and `OAI.UniversalTensorSquare.sg8660` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean (declaration OAI.UniversalTensorSquare.sg67)

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

lemma sg67 : RowSquare [3,1,1,1] [2,2,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
