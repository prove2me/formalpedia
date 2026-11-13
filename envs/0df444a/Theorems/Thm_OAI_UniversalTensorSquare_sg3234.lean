-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg3234
-- name    : OAI.UniversalTensorSquare.sg3234
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T13:05:38.157314+00:00
-- url     : https://prove2.me/theorems/fe9bcde7-77f1-487c-ac3e-e7becc3e5370
-- title:
--   OAI.UniversalTensorSquare.sg3234: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg3234` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes6.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes6.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg3234 : RowSquare [4,4,2,1,1,1,1,1] [8,7]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_50All`, `OAI.UniversalTensorSquare.sg22431`, `OAI.UniversalTensorSquare.sg27657`, `OAI.UniversalTensorSquare.sg27717`, `OAI.UniversalTensorSquare.sg27767`, `OAI.UniversalTensorSquare.sg27806`, `OAI.UniversalTensorSquare.sg27949`, `OAI.UniversalTensorSquare.sg27997`, `OAI.UniversalTensorSquare.sg28149`, `OAI.UniversalTensorSquare.sg28441`, `OAI.UniversalTensorSquare.sg28487`, `OAI.UniversalTensorSquare.sg29157` and `OAI.UniversalTensorSquare.sg29961` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes6.lean (declaration OAI.UniversalTensorSquare.sg3234)

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

lemma sg3234 : RowSquare [4,4,2,1,1,1,1,1] [8,7] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
