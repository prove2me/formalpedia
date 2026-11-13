-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg8660
-- name    : OAI.UniversalTensorSquare.sg8660
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:49:01.425881+00:00
-- url     : https://prove2.me/theorems/a303f3b9-d5cc-41a3-9e58-d22107bcecc9
-- title:
--   OAI.UniversalTensorSquare.sg8660: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg8660` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes20.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes20.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg8660 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,4,3,2,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_633All`, `OAI.UniversalTensorSquare.sg24818`, `OAI.UniversalTensorSquare.sg24865`, `OAI.UniversalTensorSquare.sg27190`, `OAI.UniversalTensorSquare.sg27208`, `OAI.UniversalTensorSquare.sg27333`, `OAI.UniversalTensorSquare.sg27362`, `OAI.UniversalTensorSquare.sg27412`, `OAI.UniversalTensorSquare.sg30312`, `OAI.UniversalTensorSquare.sg30478`, `OAI.UniversalTensorSquare.sg30876`, `OAI.UniversalTensorSquare.sg31003`, `OAI.UniversalTensorSquare.sg31184`, `OAI.UniversalTensorSquare.sg31264`, `OAI.UniversalTensorSquare.sg31288`, `OAI.UniversalTensorSquare.sg31357`, `OAI.UniversalTensorSquare.sg31377`, `OAI.UniversalTensorSquare.sg31399` and `OAI.UniversalTensorSquare.sg31776` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes20.lean (declaration OAI.UniversalTensorSquare.sg8660)

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

lemma sg8660 : RowSquare [6,5,2,2,1,1,1,1,1,1] [4,4,3,2,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
