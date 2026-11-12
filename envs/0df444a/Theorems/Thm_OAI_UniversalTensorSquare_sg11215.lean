-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg11215
-- name    : OAI.UniversalTensorSquare.sg11215
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T20:36:20.017194+00:00
-- url     : https://prove2.me/theorems/ba2a6b19-5f9f-47d7-ad56-4c7e7493eadb
-- title:
--   OAI.UniversalTensorSquare.sg11215: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg11215` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes26.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes26.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg11215 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,3,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_486All`, `OAI.UniversalTensorSquare.degreeTree62_489All`, `OAI.UniversalTensorSquare.degreeTree62_503All`, `OAI.UniversalTensorSquare.degreeTree62_505All`, `OAI.UniversalTensorSquare.degreeTree62_789All`, `OAI.UniversalTensorSquare.sg37419`, `OAI.UniversalTensorSquare.sg37422`, `OAI.UniversalTensorSquare.sg37425`, `OAI.UniversalTensorSquare.sg37427` and `OAI.UniversalTensorSquare.sg40722` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes26.lean (declaration OAI.UniversalTensorSquare.sg11215)

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

lemma sg11215 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,3,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
