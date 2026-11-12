-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg1036
-- name    : OAI.UniversalTensorSquare.sg1036
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T20:28:25.821918+00:00
-- url     : https://prove2.me/theorems/a11c7ff7-58ae-442b-9e6c-2653f09ed958
-- title:
--   OAI.UniversalTensorSquare.sg1036: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg1036` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg1036 : RowSquare [6,2,1,1] [3,2,2,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_103All`, `OAI.UniversalTensorSquare.degreeTree41_12All`, `OAI.UniversalTensorSquare.degreeTree43_362All`, `OAI.UniversalTensorSquare.degreeTree43_417All`, `OAI.UniversalTensorSquare.degreeTree43_607All`, `OAI.UniversalTensorSquare.degreeTree43_623All`, `OAI.UniversalTensorSquare.degreeTree43_627All`, `OAI.UniversalTensorSquare.degreeTree43_634All`, `OAI.UniversalTensorSquare.degreeTree43_638All`, `OAI.UniversalTensorSquare.sg21867`, `OAI.UniversalTensorSquare.sg22838`, `OAI.UniversalTensorSquare.sg23047`, `OAI.UniversalTensorSquare.sg23183`, `OAI.UniversalTensorSquare.sg23191`, `OAI.UniversalTensorSquare.sg28968`, `OAI.UniversalTensorSquare.sg29631`, `OAI.UniversalTensorSquare.sg29632`, `OAI.UniversalTensorSquare.sg30321`, `OAI.UniversalTensorSquare.sg30349`, `OAI.UniversalTensorSquare.sg30361`, `OAI.UniversalTensorSquare.sg30885`, `OAI.UniversalTensorSquare.sg30913`, `OAI.UniversalTensorSquare.sg30925`, `OAI.UniversalTensorSquare.sg31443`, `OAI.UniversalTensorSquare.sg31445`, `OAI.UniversalTensorSquare.sg31448`, `OAI.UniversalTensorSquare.sg31449`, `OAI.UniversalTensorSquare.sg31450` and `OAI.UniversalTensorSquare.sg31671` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes1.lean (declaration OAI.UniversalTensorSquare.sg1036)

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

lemma sg1036 : RowSquare [6,2,1,1] [3,2,2,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
