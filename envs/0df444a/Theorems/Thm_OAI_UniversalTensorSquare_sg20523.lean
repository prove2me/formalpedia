-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg20523
-- name    : OAI.UniversalTensorSquare.sg20523
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:51:52.277018+00:00
-- url     : https://prove2.me/theorems/a5f975c5-2cb9-4f82-9305-9f80f376abd6
-- title:
--   OAI.UniversalTensorSquare.sg20523: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg20523` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg20523 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,3,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_0All`, `OAI.UniversalTensorSquare.degreeTree62_120All`, `OAI.UniversalTensorSquare.degreeTree62_137All`, `OAI.UniversalTensorSquare.degreeTree62_138All`, `OAI.UniversalTensorSquare.degreeTree62_13All`, `OAI.UniversalTensorSquare.degreeTree62_142All`, `OAI.UniversalTensorSquare.degreeTree62_148All`, `OAI.UniversalTensorSquare.degreeTree62_176All`, `OAI.UniversalTensorSquare.degreeTree62_178All`, `OAI.UniversalTensorSquare.degreeTree62_201All`, `OAI.UniversalTensorSquare.degreeTree62_20All`, `OAI.UniversalTensorSquare.degreeTree62_216All`, `OAI.UniversalTensorSquare.degreeTree62_217All`, `OAI.UniversalTensorSquare.degreeTree62_229All`, `OAI.UniversalTensorSquare.degreeTree62_233All`, `OAI.UniversalTensorSquare.degreeTree62_263All`, `OAI.UniversalTensorSquare.degreeTree62_277All`, `OAI.UniversalTensorSquare.degreeTree62_279All`, `OAI.UniversalTensorSquare.degreeTree62_290All`, `OAI.UniversalTensorSquare.degreeTree62_291All`, `OAI.UniversalTensorSquare.degreeTree62_293All`, `OAI.UniversalTensorSquare.degreeTree62_2All`, `OAI.UniversalTensorSquare.degreeTree62_302All`, `OAI.UniversalTensorSquare.degreeTree62_307All`, `OAI.UniversalTensorSquare.degreeTree62_309All`, `OAI.UniversalTensorSquare.degreeTree62_310All`, `OAI.UniversalTensorSquare.degreeTree62_317All`, `OAI.UniversalTensorSquare.degreeTree62_39All`, `OAI.UniversalTensorSquare.degreeTree62_4All`, `OAI.UniversalTensorSquare.degreeTree62_515All`, `OAI.UniversalTensorSquare.degreeTree62_614All`, `OAI.UniversalTensorSquare.degreeTree62_625All`, `OAI.UniversalTensorSquare.degreeTree62_680All`, `OAI.UniversalTensorSquare.degreeTree62_713All`, `OAI.UniversalTensorSquare.degreeTree62_719All`, `OAI.UniversalTensorSquare.degreeTree62_722All`, `OAI.UniversalTensorSquare.degreeTree62_77All`, `OAI.UniversalTensorSquare.degreeTree62_852All`, `OAI.UniversalTensorSquare.degreeTree62_860All`, `OAI.UniversalTensorSquare.degreeTree62_893All`, `OAI.UniversalTensorSquare.degreeTree62_89All`, `OAI.UniversalTensorSquare.degreeTree62_939All`, `OAI.UniversalTensorSquare.degreeTree62_953All`, `OAI.UniversalTensorSquare.degreeTree62_956All`, `OAI.UniversalTensorSquare.degreeTree62_96All`, `OAI.UniversalTensorSquare.sg32017`, `OAI.UniversalTensorSquare.sg32249`, `OAI.UniversalTensorSquare.sg32294`, `OAI.UniversalTensorSquare.sg32672`, `OAI.UniversalTensorSquare.sg32695`, `OAI.UniversalTensorSquare.sg32710`, `OAI.UniversalTensorSquare.sg32855`, `OAI.UniversalTensorSquare.sg33415`, `OAI.UniversalTensorSquare.sg33794`, `OAI.UniversalTensorSquare.sg34415`, `OAI.UniversalTensorSquare.sg37712`, `OAI.UniversalTensorSquare.sg38918`, `OAI.UniversalTensorSquare.sg41503`, `OAI.UniversalTensorSquare.sg42030`, `OAI.UniversalTensorSquare.sg42080`, `OAI.UniversalTensorSquare.sg42085`, `OAI.UniversalTensorSquare.sg42088`, `OAI.UniversalTensorSquare.sg42508`, `OAI.UniversalTensorSquare.sg42545` and `OAI.UniversalTensorSquare.sg42548` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean (declaration OAI.UniversalTensorSquare.sg20523)

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

lemma sg20523 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,3,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
