-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg8058
-- name    : OAI.UniversalTensorSquare.sg8058
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:46:39.219209+00:00
-- url     : https://prove2.me/theorems/02e5b445-97f7-4ae9-8950-ef64fae9366f
-- title:
--   OAI.UniversalTensorSquare.sg8058: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg8058` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes18.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes18.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg8058 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [7,7,2,2,2,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg40027`, `OAI.UniversalTensorSquare.sg40029`, `OAI.UniversalTensorSquare.sg40030`, `OAI.UniversalTensorSquare.sg40086`, `OAI.UniversalTensorSquare.sg40097`, `OAI.UniversalTensorSquare.sg40099`, `OAI.UniversalTensorSquare.sg40100`, `OAI.UniversalTensorSquare.sg40149`, `OAI.UniversalTensorSquare.sg40165`, `OAI.UniversalTensorSquare.sg40167`, `OAI.UniversalTensorSquare.sg40168` and `OAI.UniversalTensorSquare.sg42578` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes18.lean (declaration OAI.UniversalTensorSquare.sg8058)

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

lemma sg8058 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [7,7,2,2,2,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
