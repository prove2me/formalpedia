-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg6768
-- name    : OAI.UniversalTensorSquare.sg6768
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:27:22.569014+00:00
-- url     : https://prove2.me/theorems/177775ad-135b-4a83-87de-ee4b2fe84bfe
-- title:
--   OAI.UniversalTensorSquare.sg6768: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg6768` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes15.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes15.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg6768 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_10All`, `OAI.UniversalTensorSquare.degreeTree39_1All`, `OAI.UniversalTensorSquare.sg21678`, `OAI.UniversalTensorSquare.sg21725`, `OAI.UniversalTensorSquare.sg21731`, `OAI.UniversalTensorSquare.sg21736` and `OAI.UniversalTensorSquare.sg21848` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes15.lean (declaration OAI.UniversalTensorSquare.sg6768)

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

lemma sg6768 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
