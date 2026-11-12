-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg20526
-- name    : OAI.UniversalTensorSquare.sg20526
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:51:52.081198+00:00
-- url     : https://prove2.me/theorems/283c87f5-a566-48db-a24b-0f747a0a57fc
-- title:
--   OAI.UniversalTensorSquare.sg20526: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg20526` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg20526 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,4,2,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_127All`, `OAI.UniversalTensorSquare.degreeTree62_138All`, `OAI.UniversalTensorSquare.degreeTree62_13All`, `OAI.UniversalTensorSquare.degreeTree62_142All`, `OAI.UniversalTensorSquare.degreeTree62_143All`, `OAI.UniversalTensorSquare.degreeTree62_16All`, `OAI.UniversalTensorSquare.degreeTree62_174All`, `OAI.UniversalTensorSquare.degreeTree62_176All`, `OAI.UniversalTensorSquare.degreeTree62_178All`, `OAI.UniversalTensorSquare.degreeTree62_201All`, `OAI.UniversalTensorSquare.degreeTree62_216All`, `OAI.UniversalTensorSquare.degreeTree62_229All`, `OAI.UniversalTensorSquare.degreeTree62_22All`, `OAI.UniversalTensorSquare.degreeTree62_230All`, `OAI.UniversalTensorSquare.degreeTree62_233All`, `OAI.UniversalTensorSquare.degreeTree62_267All`, `OAI.UniversalTensorSquare.degreeTree62_274All`, `OAI.UniversalTensorSquare.degreeTree62_277All`, `OAI.UniversalTensorSquare.degreeTree62_279All`, `OAI.UniversalTensorSquare.degreeTree62_290All`, `OAI.UniversalTensorSquare.degreeTree62_293All`, `OAI.UniversalTensorSquare.degreeTree62_2All`, `OAI.UniversalTensorSquare.degreeTree62_302All`, `OAI.UniversalTensorSquare.degreeTree62_307All`, `OAI.UniversalTensorSquare.degreeTree62_309All`, `OAI.UniversalTensorSquare.degreeTree62_310All`, `OAI.UniversalTensorSquare.degreeTree62_394All`, `OAI.UniversalTensorSquare.degreeTree62_39All`, `OAI.UniversalTensorSquare.degreeTree62_3All`, `OAI.UniversalTensorSquare.degreeTree62_55All`, `OAI.UniversalTensorSquare.degreeTree62_65All`, `OAI.UniversalTensorSquare.degreeTree62_72All`, `OAI.UniversalTensorSquare.degreeTree62_75All`, `OAI.UniversalTensorSquare.degreeTree62_84All`, `OAI.UniversalTensorSquare.degreeTree62_89All`, `OAI.UniversalTensorSquare.degreeTree62_8All`, `OAI.UniversalTensorSquare.sg32015`, `OAI.UniversalTensorSquare.sg32016`, `OAI.UniversalTensorSquare.sg32022`, `OAI.UniversalTensorSquare.sg32132`, `OAI.UniversalTensorSquare.sg32135`, `OAI.UniversalTensorSquare.sg32136`, `OAI.UniversalTensorSquare.sg32151`, `OAI.UniversalTensorSquare.sg32152`, `OAI.UniversalTensorSquare.sg32162`, `OAI.UniversalTensorSquare.sg32401`, `OAI.UniversalTensorSquare.sg32677`, `OAI.UniversalTensorSquare.sg32700`, `OAI.UniversalTensorSquare.sg32715`, `OAI.UniversalTensorSquare.sg32725`, `OAI.UniversalTensorSquare.sg32726`, `OAI.UniversalTensorSquare.sg32741`, `OAI.UniversalTensorSquare.sg32742`, `OAI.UniversalTensorSquare.sg32860`, `OAI.UniversalTensorSquare.sg32877`, `OAI.UniversalTensorSquare.sg33085`, `OAI.UniversalTensorSquare.sg33096`, `OAI.UniversalTensorSquare.sg33397`, `OAI.UniversalTensorSquare.sg33612`, `OAI.UniversalTensorSquare.sg33685`, `OAI.UniversalTensorSquare.sg33799`, `OAI.UniversalTensorSquare.sg34420`, `OAI.UniversalTensorSquare.sg34595` and `OAI.UniversalTensorSquare.sg35211` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean (declaration OAI.UniversalTensorSquare.sg20526)

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

lemma sg20526 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,4,2,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
