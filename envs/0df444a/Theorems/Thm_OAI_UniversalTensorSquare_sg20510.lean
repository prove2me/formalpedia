-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg20510
-- name    : OAI.UniversalTensorSquare.sg20510
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:51:04.846024+00:00
-- url     : https://prove2.me/theorems/6cc0b96c-fe95-4775-8352-87ef538f9411
-- title:
--   OAI.UniversalTensorSquare.sg20510: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg20510` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg20510 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,2,2,2,2,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_105All`, `OAI.UniversalTensorSquare.degreeTree62_114All`, `OAI.UniversalTensorSquare.degreeTree62_122All`, `OAI.UniversalTensorSquare.degreeTree62_184All`, `OAI.UniversalTensorSquare.degreeTree62_196All`, `OAI.UniversalTensorSquare.degreeTree62_201All`, `OAI.UniversalTensorSquare.degreeTree62_209All`, `OAI.UniversalTensorSquare.degreeTree62_217All`, `OAI.UniversalTensorSquare.degreeTree62_238All`, `OAI.UniversalTensorSquare.degreeTree62_23All`, `OAI.UniversalTensorSquare.degreeTree62_249All`, `OAI.UniversalTensorSquare.degreeTree62_253All`, `OAI.UniversalTensorSquare.degreeTree62_255All`, `OAI.UniversalTensorSquare.degreeTree62_258All`, `OAI.UniversalTensorSquare.degreeTree62_261All`, `OAI.UniversalTensorSquare.degreeTree62_262All`, `OAI.UniversalTensorSquare.degreeTree62_271All`, `OAI.UniversalTensorSquare.degreeTree62_274All`, `OAI.UniversalTensorSquare.degreeTree62_277All`, `OAI.UniversalTensorSquare.degreeTree62_283All`, `OAI.UniversalTensorSquare.degreeTree62_288All`, `OAI.UniversalTensorSquare.degreeTree62_291All`, `OAI.UniversalTensorSquare.degreeTree62_298All`, `OAI.UniversalTensorSquare.degreeTree62_34All`, `OAI.UniversalTensorSquare.degreeTree62_486All`, `OAI.UniversalTensorSquare.degreeTree62_692All`, `OAI.UniversalTensorSquare.degreeTree62_840All`, `OAI.UniversalTensorSquare.degreeTree62_880All`, `OAI.UniversalTensorSquare.degreeTree62_953All`, `OAI.UniversalTensorSquare.degreeTree62_967All`, `OAI.UniversalTensorSquare.degreeTree62_971All`, `OAI.UniversalTensorSquare.degreeTree62_982All`, `OAI.UniversalTensorSquare.sg32297`, `OAI.UniversalTensorSquare.sg32359`, `OAI.UniversalTensorSquare.sg32372`, `OAI.UniversalTensorSquare.sg32451`, `OAI.UniversalTensorSquare.sg33125`, `OAI.UniversalTensorSquare.sg33167`, `OAI.UniversalTensorSquare.sg33369`, `OAI.UniversalTensorSquare.sg33399`, `OAI.UniversalTensorSquare.sg33759`, `OAI.UniversalTensorSquare.sg34205`, `OAI.UniversalTensorSquare.sg34750`, `OAI.UniversalTensorSquare.sg34808`, `OAI.UniversalTensorSquare.sg34914`, `OAI.UniversalTensorSquare.sg34953`, `OAI.UniversalTensorSquare.sg34990`, `OAI.UniversalTensorSquare.sg35278`, `OAI.UniversalTensorSquare.sg35323`, `OAI.UniversalTensorSquare.sg38563`, `OAI.UniversalTensorSquare.sg38662`, `OAI.UniversalTensorSquare.sg39345`, `OAI.UniversalTensorSquare.sg39771`, `OAI.UniversalTensorSquare.sg41360`, `OAI.UniversalTensorSquare.sg41928`, `OAI.UniversalTensorSquare.sg41979`, `OAI.UniversalTensorSquare.sg42272`, `OAI.UniversalTensorSquare.sg42395`, `OAI.UniversalTensorSquare.sg42422`, `OAI.UniversalTensorSquare.sg42466`, `OAI.UniversalTensorSquare.sg42928`, `OAI.UniversalTensorSquare.sg43040`, `OAI.UniversalTensorSquare.sg43083` and `OAI.UniversalTensorSquare.sg43121` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean (declaration OAI.UniversalTensorSquare.sg20510)

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

lemma sg20510 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,2,2,2,2,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
