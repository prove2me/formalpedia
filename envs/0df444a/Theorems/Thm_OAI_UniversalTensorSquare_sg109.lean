-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg109
-- name    : OAI.UniversalTensorSquare.sg109
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T20:32:52.487215+00:00
-- url     : https://prove2.me/theorems/760acabe-9349-4320-9874-e0484825c66e
-- title:
--   OAI.UniversalTensorSquare.sg109: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg109` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg109 : RowSquare [1,1,1,1,1,1,1] [7]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_146All`, `OAI.UniversalTensorSquare.degreeTree62_147All`, `OAI.UniversalTensorSquare.degreeTree62_150All`, `OAI.UniversalTensorSquare.degreeTree62_166All`, `OAI.UniversalTensorSquare.degreeTree62_174All`, `OAI.UniversalTensorSquare.degreeTree62_193All`, `OAI.UniversalTensorSquare.degreeTree62_199All`, `OAI.UniversalTensorSquare.degreeTree62_207All`, `OAI.UniversalTensorSquare.degreeTree62_210All`, `OAI.UniversalTensorSquare.degreeTree62_212All`, `OAI.UniversalTensorSquare.degreeTree62_220All`, `OAI.UniversalTensorSquare.degreeTree62_225All`, `OAI.UniversalTensorSquare.degreeTree62_227All`, `OAI.UniversalTensorSquare.degreeTree62_351All`, `OAI.UniversalTensorSquare.degreeTree62_621All`, `OAI.UniversalTensorSquare.degreeTree62_713All`, `OAI.UniversalTensorSquare.degreeTree62_719All`, `OAI.UniversalTensorSquare.sg1175`, `OAI.UniversalTensorSquare.sg12702`, `OAI.UniversalTensorSquare.sg14546`, `OAI.UniversalTensorSquare.sg18916`, `OAI.UniversalTensorSquare.sg18917`, `OAI.UniversalTensorSquare.sg20507`, `OAI.UniversalTensorSquare.sg2100`, `OAI.UniversalTensorSquare.sg2103`, `OAI.UniversalTensorSquare.sg2507`, `OAI.UniversalTensorSquare.sg31927`, `OAI.UniversalTensorSquare.sg32177`, `OAI.UniversalTensorSquare.sg32229`, `OAI.UniversalTensorSquare.sg33056`, `OAI.UniversalTensorSquare.sg33644`, `OAI.UniversalTensorSquare.sg33758`, `OAI.UniversalTensorSquare.sg33764`, `OAI.UniversalTensorSquare.sg33925`, `OAI.UniversalTensorSquare.sg34003`, `OAI.UniversalTensorSquare.sg34035`, `OAI.UniversalTensorSquare.sg35532`, `OAI.UniversalTensorSquare.sg36611`, `OAI.UniversalTensorSquare.sg36616` and `OAI.UniversalTensorSquare.sg40259` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg109)

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

lemma sg109 : RowSquare [1,1,1,1,1,1,1] [7] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
