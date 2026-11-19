-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg637
-- name    : OAI.UniversalTensorSquare.sg637
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T22:55:23.721895+00:00
-- url     : https://prove2.me/theorems/c235efe7-7ab1-434c-a803-698281f2c7b1
-- title:
--   OAI.UniversalTensorSquare.sg637: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg637` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg637 : RowSquare [5,2,2] [2,2,2,2,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_421All`, `OAI.UniversalTensorSquare.degreeTree43_489All`, `OAI.UniversalTensorSquare.degreeTree62_60All`, `OAI.UniversalTensorSquare.sg17647`, `OAI.UniversalTensorSquare.sg24427`, `OAI.UniversalTensorSquare.sg25042`, `OAI.UniversalTensorSquare.sg34511`, `OAI.UniversalTensorSquare.sg34568`, `OAI.UniversalTensorSquare.sg35150`, `OAI.UniversalTensorSquare.sg35311`, `OAI.UniversalTensorSquare.sg35313`, `OAI.UniversalTensorSquare.sg35334`, `OAI.UniversalTensorSquare.sg35336`, `OAI.UniversalTensorSquare.sg35445`, `OAI.UniversalTensorSquare.sg35461`, `OAI.UniversalTensorSquare.sg37631`, `OAI.UniversalTensorSquare.sg37642`, `OAI.UniversalTensorSquare.sg41481`, `OAI.UniversalTensorSquare.sg41485`, `OAI.UniversalTensorSquare.sg41977` and `OAI.UniversalTensorSquare.sg42077` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean (declaration OAI.UniversalTensorSquare.sg637)

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

lemma sg637 : RowSquare [5,2,2] [2,2,2,2,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
