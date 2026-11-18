-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg3533
-- name    : OAI.UniversalTensorSquare.sg3533
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T10:47:53.299316+00:00
-- url     : https://prove2.me/theorems/345ee68f-c94d-427d-8990-dae659abdc9f
-- title:
--   OAI.UniversalTensorSquare.sg3533: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg3533` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg3533 : RowSquare [8,2,1,1,1,1,1] [3,2,2,2,2,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_320All`, `OAI.UniversalTensorSquare.degreeTree62_364All`, `OAI.UniversalTensorSquare.degreeTree62_534All`, `OAI.UniversalTensorSquare.sg19628`, `OAI.UniversalTensorSquare.sg35607`, `OAI.UniversalTensorSquare.sg35722`, `OAI.UniversalTensorSquare.sg35728`, `OAI.UniversalTensorSquare.sg35783`, `OAI.UniversalTensorSquare.sg35930`, `OAI.UniversalTensorSquare.sg36202`, `OAI.UniversalTensorSquare.sg36207`, `OAI.UniversalTensorSquare.sg36550`, `OAI.UniversalTensorSquare.sg36555`, `OAI.UniversalTensorSquare.sg36733`, `OAI.UniversalTensorSquare.sg36738`, `OAI.UniversalTensorSquare.sg36781`, `OAI.UniversalTensorSquare.sg36786`, `OAI.UniversalTensorSquare.sg38025` and `OAI.UniversalTensorSquare.sg38433` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean (declaration OAI.UniversalTensorSquare.sg3533)

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

lemma sg3533 : RowSquare [8,2,1,1,1,1,1] [3,2,2,2,2,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
