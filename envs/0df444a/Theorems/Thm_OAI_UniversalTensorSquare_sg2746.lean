-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg2746
-- name    : OAI.UniversalTensorSquare.sg2746
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T06:29:20.095751+00:00
-- url     : https://prove2.me/theorems/dfdb6e7f-79f5-45d4-9b37-f49570b47703
-- title:
--   OAI.UniversalTensorSquare.sg2746: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg2746` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg2746 : RowSquare [7,3,2,1,1] [3,3,2,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_143All`, `OAI.UniversalTensorSquare.degreeTree62_151All`, `OAI.UniversalTensorSquare.degreeTree62_174All`, `OAI.UniversalTensorSquare.degreeTree62_195All`, `OAI.UniversalTensorSquare.degreeTree62_212All`, `OAI.UniversalTensorSquare.degreeTree62_213All`, `OAI.UniversalTensorSquare.degreeTree62_229All`, `OAI.UniversalTensorSquare.degreeTree62_349All`, `OAI.UniversalTensorSquare.degreeTree62_405All`, `OAI.UniversalTensorSquare.degreeTree62_414All`, `OAI.UniversalTensorSquare.degreeTree62_435All`, `OAI.UniversalTensorSquare.degreeTree62_533All`, `OAI.UniversalTensorSquare.degreeTree62_562All`, `OAI.UniversalTensorSquare.degreeTree62_574All`, `OAI.UniversalTensorSquare.degreeTree62_602All`, `OAI.UniversalTensorSquare.degreeTree62_610All`, `OAI.UniversalTensorSquare.degreeTree62_614All`, `OAI.UniversalTensorSquare.degreeTree62_645All`, `OAI.UniversalTensorSquare.degreeTree62_65All`, `OAI.UniversalTensorSquare.degreeTree62_742All`, `OAI.UniversalTensorSquare.degreeTree62_75All`, `OAI.UniversalTensorSquare.degreeTree62_81All`, `OAI.UniversalTensorSquare.degreeTree62_865All`, `OAI.UniversalTensorSquare.degreeTree62_942All`, `OAI.UniversalTensorSquare.sg12919`, `OAI.UniversalTensorSquare.sg14296`, `OAI.UniversalTensorSquare.sg18306`, `OAI.UniversalTensorSquare.sg19527`, `OAI.UniversalTensorSquare.sg24641`, `OAI.UniversalTensorSquare.sg26296`, `OAI.UniversalTensorSquare.sg26481`, `OAI.UniversalTensorSquare.sg33689`, `OAI.UniversalTensorSquare.sg33691`, `OAI.UniversalTensorSquare.sg33797`, `OAI.UniversalTensorSquare.sg33997`, `OAI.UniversalTensorSquare.sg35878`, `OAI.UniversalTensorSquare.sg36808`, `OAI.UniversalTensorSquare.sg36841`, `OAI.UniversalTensorSquare.sg37036`, `OAI.UniversalTensorSquare.sg37040`, `OAI.UniversalTensorSquare.sg37043`, `OAI.UniversalTensorSquare.sg37901`, `OAI.UniversalTensorSquare.sg37941`, `OAI.UniversalTensorSquare.sg37944`, `OAI.UniversalTensorSquare.sg38361`, `OAI.UniversalTensorSquare.sg38363`, `OAI.UniversalTensorSquare.sg38366`, `OAI.UniversalTensorSquare.sg38454`, `OAI.UniversalTensorSquare.sg38759`, `OAI.UniversalTensorSquare.sg38762`, `OAI.UniversalTensorSquare.sg38768`, `OAI.UniversalTensorSquare.sg38902`, `OAI.UniversalTensorSquare.sg38918`, `OAI.UniversalTensorSquare.sg38919`, `OAI.UniversalTensorSquare.sg39366`, `OAI.UniversalTensorSquare.sg41069`, `OAI.UniversalTensorSquare.sg41072`, `OAI.UniversalTensorSquare.sg41756`, `OAI.UniversalTensorSquare.sg41890`, `OAI.UniversalTensorSquare.sg41960`, `OAI.UniversalTensorSquare.sg42021`, `OAI.UniversalTensorSquare.sg42030`, `OAI.UniversalTensorSquare.sg42360` and `OAI.UniversalTensorSquare.sg42779` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes5.lean (declaration OAI.UniversalTensorSquare.sg2746)

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

lemma sg2746 : RowSquare [7,3,2,1,1] [3,3,2,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
