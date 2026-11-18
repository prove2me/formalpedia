-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg748
-- name    : OAI.UniversalTensorSquare.sg748
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T23:16:21.603653+00:00
-- url     : https://prove2.me/theorems/779b3059-6f6f-453a-a484-435a7098142e
-- title:
--   OAI.UniversalTensorSquare.sg748: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg748` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg748 : RowSquare [3,2,1,1,1,1,1] [5,5]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_255All`, `OAI.UniversalTensorSquare.degreeTree62_372All`, `OAI.UniversalTensorSquare.degreeTree62_403All`, `OAI.UniversalTensorSquare.degreeTree62_550All`, `OAI.UniversalTensorSquare.degreeTree62_922All`, `OAI.UniversalTensorSquare.degreeTree62_99All`, `OAI.UniversalTensorSquare.sg22434`, `OAI.UniversalTensorSquare.sg22435`, `OAI.UniversalTensorSquare.sg22436`, `OAI.UniversalTensorSquare.sg22437`, `OAI.UniversalTensorSquare.sg22474`, `OAI.UniversalTensorSquare.sg22475`, `OAI.UniversalTensorSquare.sg22476`, `OAI.UniversalTensorSquare.sg22477`, `OAI.UniversalTensorSquare.sg22620`, `OAI.UniversalTensorSquare.sg22621`, `OAI.UniversalTensorSquare.sg22622`, `OAI.UniversalTensorSquare.sg22623`, `OAI.UniversalTensorSquare.sg32355`, `OAI.UniversalTensorSquare.sg32724`, `OAI.UniversalTensorSquare.sg32764`, `OAI.UniversalTensorSquare.sg32899`, `OAI.UniversalTensorSquare.sg32961`, `OAI.UniversalTensorSquare.sg33635`, `OAI.UniversalTensorSquare.sg34648`, `OAI.UniversalTensorSquare.sg35543`, `OAI.UniversalTensorSquare.sg35545`, `OAI.UniversalTensorSquare.sg35546`, `OAI.UniversalTensorSquare.sg35589`, `OAI.UniversalTensorSquare.sg35638`, `OAI.UniversalTensorSquare.sg35708`, `OAI.UniversalTensorSquare.sg35709`, `OAI.UniversalTensorSquare.sg35754`, `OAI.UniversalTensorSquare.sg35755`, `OAI.UniversalTensorSquare.sg35813`, `OAI.UniversalTensorSquare.sg36229`, `OAI.UniversalTensorSquare.sg36264`, `OAI.UniversalTensorSquare.sg36405`, `OAI.UniversalTensorSquare.sg36406`, `OAI.UniversalTensorSquare.sg36590`, `OAI.UniversalTensorSquare.sg36592`, `OAI.UniversalTensorSquare.sg36840`, `OAI.UniversalTensorSquare.sg37909`, `OAI.UniversalTensorSquare.sg37968`, `OAI.UniversalTensorSquare.sg38988`, `OAI.UniversalTensorSquare.sg39164`, `OAI.UniversalTensorSquare.sg39998`, `OAI.UniversalTensorSquare.sg40046`, `OAI.UniversalTensorSquare.sg40649`, `OAI.UniversalTensorSquare.sg4167`, `OAI.UniversalTensorSquare.sg42797`, `OAI.UniversalTensorSquare.sg6471` and `OAI.UniversalTensorSquare.sg7968` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes1.lean (declaration OAI.UniversalTensorSquare.sg748)

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

lemma sg748 : RowSquare [3,2,1,1,1,1,1] [5,5] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
