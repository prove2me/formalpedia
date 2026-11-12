-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg12350
-- name    : OAI.UniversalTensorSquare.sg12350
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T20:55:41.536197+00:00
-- url     : https://prove2.me/theorems/473ee782-8a89-4dd4-ac3a-fd39acabcf48
-- title:
--   OAI.UniversalTensorSquare.sg12350: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg12350` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes29.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes29.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg12350 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,2,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg34180`, `OAI.UniversalTensorSquare.sg34811`, `OAI.UniversalTensorSquare.sg35044`, `OAI.UniversalTensorSquare.sg35046` and `OAI.UniversalTensorSquare.sg35231` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes29.lean (declaration OAI.UniversalTensorSquare.sg12350)

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

lemma sg12350 : RowSquare [3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,2,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
