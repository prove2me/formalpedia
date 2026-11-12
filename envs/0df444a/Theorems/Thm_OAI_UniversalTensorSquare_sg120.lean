-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg120
-- name    : OAI.UniversalTensorSquare.sg120
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T20:44:26.121345+00:00
-- url     : https://prove2.me/theorems/d0b7d05a-df59-4fe0-b443-f473ad8871c9
-- title:
--   OAI.UniversalTensorSquare.sg120: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg120` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg120 : RowSquare [2,2,1,1,1] [5,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree24_8All`, `OAI.UniversalTensorSquare.degreeTree26_21All`, `OAI.UniversalTensorSquare.degreeTree26_38All`, `OAI.UniversalTensorSquare.degreeTree26_9All`, `OAI.UniversalTensorSquare.sg10932`, `OAI.UniversalTensorSquare.sg11009`, `OAI.UniversalTensorSquare.sg23559`, `OAI.UniversalTensorSquare.sg31955`, `OAI.UniversalTensorSquare.sg4022`, `OAI.UniversalTensorSquare.sg5711`, `OAI.UniversalTensorSquare.sg7881`, `OAI.UniversalTensorSquare.sg7892`, `OAI.UniversalTensorSquare.sg7942` and `OAI.UniversalTensorSquare.sg7973` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean (declaration OAI.UniversalTensorSquare.sg120)

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

lemma sg120 : RowSquare [2,2,1,1,1] [5,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
