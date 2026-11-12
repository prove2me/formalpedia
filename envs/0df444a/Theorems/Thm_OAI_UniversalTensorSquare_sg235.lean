-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg235
-- name    : OAI.UniversalTensorSquare.sg235
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T00:58:14.628097+00:00
-- url     : https://prove2.me/theorems/8f7fbb50-9870-4a05-ac4b-c52400fa38eb
-- title:
--   OAI.UniversalTensorSquare.sg235: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg235` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg235 : RowSquare [1,1,1,1,1,1,1,1] [8]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_29All`, `OAI.UniversalTensorSquare.sg21214`, `OAI.UniversalTensorSquare.sg21234`, `OAI.UniversalTensorSquare.sg21247`, `OAI.UniversalTensorSquare.sg21248`, `OAI.UniversalTensorSquare.sg22439`, `OAI.UniversalTensorSquare.sg26974`, `OAI.UniversalTensorSquare.sg27006`, `OAI.UniversalTensorSquare.sg27045`, `OAI.UniversalTensorSquare.sg27652`, `OAI.UniversalTensorSquare.sg27653`, `OAI.UniversalTensorSquare.sg27659`, `OAI.UniversalTensorSquare.sg27660`, `OAI.UniversalTensorSquare.sg27720`, `OAI.UniversalTensorSquare.sg27721`, `OAI.UniversalTensorSquare.sg27727`, `OAI.UniversalTensorSquare.sg27778`, `OAI.UniversalTensorSquare.sg27779`, `OAI.UniversalTensorSquare.sg27784`, `OAI.UniversalTensorSquare.sg27825`, `OAI.UniversalTensorSquare.sg27848`, `OAI.UniversalTensorSquare.sg27960`, `OAI.UniversalTensorSquare.sg27961`, `OAI.UniversalTensorSquare.sg27966`, `OAI.UniversalTensorSquare.sg28016`, `OAI.UniversalTensorSquare.sg28460`, `OAI.UniversalTensorSquare.sg30704`, `OAI.UniversalTensorSquare.sg32233`, `OAI.UniversalTensorSquare.sg33754`, `OAI.UniversalTensorSquare.sg33998`, `OAI.UniversalTensorSquare.sg34444` and `OAI.UniversalTensorSquare.sg34607` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg235)

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

lemma sg235 : RowSquare [1,1,1,1,1,1,1,1] [8] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
