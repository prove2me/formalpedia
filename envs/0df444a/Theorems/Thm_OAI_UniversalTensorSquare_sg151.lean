-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg151
-- name    : OAI.UniversalTensorSquare.sg151
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:20:38.137569+00:00
-- url     : https://prove2.me/theorems/fcda265d-a8d8-4c89-a242-214bf8827d99
-- title:
--   OAI.UniversalTensorSquare.sg151: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg151` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg151 : RowSquare [3,2,1,1] [4,3]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_372All`, `OAI.UniversalTensorSquare.degreeTree43_374All`, `OAI.UniversalTensorSquare.degreeTree43_637All`, `OAI.UniversalTensorSquare.degreeTree62_394All`, `OAI.UniversalTensorSquare.degreeTree62_755All`, `OAI.UniversalTensorSquare.sg10932`, `OAI.UniversalTensorSquare.sg11009`, `OAI.UniversalTensorSquare.sg11938`, `OAI.UniversalTensorSquare.sg11946`, `OAI.UniversalTensorSquare.sg11977`, `OAI.UniversalTensorSquare.sg12028`, `OAI.UniversalTensorSquare.sg21493`, `OAI.UniversalTensorSquare.sg22897`, `OAI.UniversalTensorSquare.sg22898`, `OAI.UniversalTensorSquare.sg22899`, `OAI.UniversalTensorSquare.sg28420`, `OAI.UniversalTensorSquare.sg28421`, `OAI.UniversalTensorSquare.sg28423`, `OAI.UniversalTensorSquare.sg37715`, `OAI.UniversalTensorSquare.sg38922`, `OAI.UniversalTensorSquare.sg40784`, `OAI.UniversalTensorSquare.sg42091`, `OAI.UniversalTensorSquare.sg7881`, `OAI.UniversalTensorSquare.sg7892`, `OAI.UniversalTensorSquare.sg7942` and `OAI.UniversalTensorSquare.sg7973` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean (declaration OAI.UniversalTensorSquare.sg151)

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

lemma sg151 : RowSquare [3,2,1,1] [4,3] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
