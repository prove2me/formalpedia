-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg18285
-- name    : OAI.UniversalTensorSquare.sg18285
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:39:44.424503+00:00
-- url     : https://prove2.me/theorems/0e2030e8-7d28-416e-853a-5985c30a724b
-- title:
--   OAI.UniversalTensorSquare.sg18285: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg18285` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes44.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes44.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg18285 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [4,4,3,3,3,3,3,2,2,2,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_162All`, `OAI.UniversalTensorSquare.degreeTree62_165All`, `OAI.UniversalTensorSquare.degreeTree62_205All`, `OAI.UniversalTensorSquare.degreeTree62_227All`, `OAI.UniversalTensorSquare.degreeTree62_80All`, `OAI.UniversalTensorSquare.sg32187`, `OAI.UniversalTensorSquare.sg32196`, `OAI.UniversalTensorSquare.sg32242`, `OAI.UniversalTensorSquare.sg33062`, `OAI.UniversalTensorSquare.sg33648`, `OAI.UniversalTensorSquare.sg33657`, `OAI.UniversalTensorSquare.sg33893`, `OAI.UniversalTensorSquare.sg33902`, `OAI.UniversalTensorSquare.sg33938`, `OAI.UniversalTensorSquare.sg33973`, `OAI.UniversalTensorSquare.sg34252`, `OAI.UniversalTensorSquare.sg34512`, `OAI.UniversalTensorSquare.sg34537`, `OAI.UniversalTensorSquare.sg36590`, `OAI.UniversalTensorSquare.sg36773`, `OAI.UniversalTensorSquare.sg37057`, `OAI.UniversalTensorSquare.sg37909` and `OAI.UniversalTensorSquare.sg37958` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes44.lean (declaration OAI.UniversalTensorSquare.sg18285)

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

lemma sg18285 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [4,4,3,3,3,3,3,2,2,2,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
