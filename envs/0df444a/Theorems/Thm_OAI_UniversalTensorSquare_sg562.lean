-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg562
-- name    : OAI.UniversalTensorSquare.sg562
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T22:43:58.518736+00:00
-- url     : https://prove2.me/theorems/6a8ade7f-98af-431a-838d-cd4abe52af74
-- title:
--   OAI.UniversalTensorSquare.sg562: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg562` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg562 : RowSquare [4,3,1,1] [2,2,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_60All`, `OAI.UniversalTensorSquare.degreeTree41_0All`, `OAI.UniversalTensorSquare.degreeTree43_441All`, `OAI.UniversalTensorSquare.degreeTree43_442All`, `OAI.UniversalTensorSquare.degreeTree43_551All`, `OAI.UniversalTensorSquare.degreeTree43_593All`, `OAI.UniversalTensorSquare.degree_pos14`, `OAI.UniversalTensorSquare.sg23505`, `OAI.UniversalTensorSquare.sg23556`, `OAI.UniversalTensorSquare.sg23565`, `OAI.UniversalTensorSquare.sg23572`, `OAI.UniversalTensorSquare.sg26962`, `OAI.UniversalTensorSquare.sg26992`, `OAI.UniversalTensorSquare.sg27000`, `OAI.UniversalTensorSquare.sg27006`, `OAI.UniversalTensorSquare.sg27008`, `OAI.UniversalTensorSquare.sg27010`, `OAI.UniversalTensorSquare.sg27042`, `OAI.UniversalTensorSquare.sg27070`, `OAI.UniversalTensorSquare.sg27965`, `OAI.UniversalTensorSquare.sg30732`, `OAI.UniversalTensorSquare.sg30739`, `OAI.UniversalTensorSquare.sg30779`, `OAI.UniversalTensorSquare.sg30804`, `OAI.UniversalTensorSquare.sg31115`, `OAI.UniversalTensorSquare.sg31126`, `OAI.UniversalTensorSquare.sg31136`, `OAI.UniversalTensorSquare.sg42700` and `OAI.UniversalTensorSquare.sg43223` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean (declaration OAI.UniversalTensorSquare.sg562)

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

lemma sg562 : RowSquare [4,3,1,1] [2,2,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
