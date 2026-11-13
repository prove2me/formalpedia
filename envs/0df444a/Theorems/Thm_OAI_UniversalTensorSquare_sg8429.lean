-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg8429
-- name    : OAI.UniversalTensorSquare.sg8429
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:47:13.367329+00:00
-- url     : https://prove2.me/theorems/7a05aac1-d540-4a62-a905-56a37f57806f
-- title:
--   OAI.UniversalTensorSquare.sg8429: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg8429` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg8429 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,3,3,3,3,2,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_109All`, `OAI.UniversalTensorSquare.degreeTree43_194All`, `OAI.UniversalTensorSquare.degreeTree43_198All`, `OAI.UniversalTensorSquare.degreeTree43_237All`, `OAI.UniversalTensorSquare.degreeTree43_238All`, `OAI.UniversalTensorSquare.degreeTree43_242All`, `OAI.UniversalTensorSquare.degreeTree43_244All`, `OAI.UniversalTensorSquare.degreeTree43_298All`, `OAI.UniversalTensorSquare.degreeTree43_299All`, `OAI.UniversalTensorSquare.degreeTree43_324All`, `OAI.UniversalTensorSquare.degreeTree43_61All`, `OAI.UniversalTensorSquare.degreeTree43_63All`, `OAI.UniversalTensorSquare.sg23691`, `OAI.UniversalTensorSquare.sg25015`, `OAI.UniversalTensorSquare.sg26204`, `OAI.UniversalTensorSquare.sg26211` and `OAI.UniversalTensorSquare.sg27541` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean (declaration OAI.UniversalTensorSquare.sg8429)

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

lemma sg8429 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,3,3,3,3,2,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
