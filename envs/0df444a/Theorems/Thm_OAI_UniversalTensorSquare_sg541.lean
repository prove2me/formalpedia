-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg541
-- name    : OAI.UniversalTensorSquare.sg541
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T22:41:05.102536+00:00
-- url     : https://prove2.me/theorems/8e4e2303-a52d-4103-bdb9-1523b3665d14
-- title:
--   OAI.UniversalTensorSquare.sg541: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg541` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg541 : RowSquare [4,2,1,1,1] [3,3,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_224All`, `OAI.UniversalTensorSquare.degreeTree43_277All`, `OAI.UniversalTensorSquare.degreeTree43_283All`, `OAI.UniversalTensorSquare.degreeTree43_587All`, `OAI.UniversalTensorSquare.degreeTree43_595All`, `OAI.UniversalTensorSquare.degreeTree43_598All`, `OAI.UniversalTensorSquare.degreeTree43_601All`, `OAI.UniversalTensorSquare.degreeTree62_662All`, `OAI.UniversalTensorSquare.sg22917`, `OAI.UniversalTensorSquare.sg22955`, `OAI.UniversalTensorSquare.sg23000`, `OAI.UniversalTensorSquare.sg23486`, `OAI.UniversalTensorSquare.sg24731`, `OAI.UniversalTensorSquare.sg27119`, `OAI.UniversalTensorSquare.sg27300`, `OAI.UniversalTensorSquare.sg27452`, `OAI.UniversalTensorSquare.sg27501`, `OAI.UniversalTensorSquare.sg29295`, `OAI.UniversalTensorSquare.sg30459`, `OAI.UniversalTensorSquare.sg31238`, `OAI.UniversalTensorSquare.sg31339` and `OAI.UniversalTensorSquare.sg42170` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean (declaration OAI.UniversalTensorSquare.sg541)

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

lemma sg541 : RowSquare [4,2,1,1,1] [3,3,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
