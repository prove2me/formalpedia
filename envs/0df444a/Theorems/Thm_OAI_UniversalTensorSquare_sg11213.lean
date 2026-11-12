-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg11213
-- name    : OAI.UniversalTensorSquare.sg11213
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T20:36:07.616599+00:00
-- url     : https://prove2.me/theorems/f520e3ed-baf1-4f0e-89f1-b36cc4b50737
-- title:
--   OAI.UniversalTensorSquare.sg11213: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg11213` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes26.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes26.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg11213 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [7,4,4,3,3,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_471All`, `OAI.UniversalTensorSquare.degreeTree62_483All`, `OAI.UniversalTensorSquare.degreeTree62_490All`, `OAI.UniversalTensorSquare.sg37252`, `OAI.UniversalTensorSquare.sg37259`, `OAI.UniversalTensorSquare.sg37262`, `OAI.UniversalTensorSquare.sg37264`, `OAI.UniversalTensorSquare.sg41714`, `OAI.UniversalTensorSquare.sg41718` and `OAI.UniversalTensorSquare.sg41720` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes26.lean (declaration OAI.UniversalTensorSquare.sg11213)

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

lemma sg11213 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [7,4,4,3,3,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
