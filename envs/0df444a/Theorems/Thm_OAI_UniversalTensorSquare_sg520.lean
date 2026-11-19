-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg520
-- name    : OAI.UniversalTensorSquare.sg520
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T22:38:10.538669+00:00
-- url     : https://prove2.me/theorems/732e6373-1622-40f2-865c-5cbab2e0aaea
-- title:
--   OAI.UniversalTensorSquare.sg520: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg520` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg520 : RowSquare [4,1,1,1,1,1] [3,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_185All`, `OAI.UniversalTensorSquare.degreeTree43_215All`, `OAI.UniversalTensorSquare.degreeTree43_228All`, `OAI.UniversalTensorSquare.degreeTree43_277All`, `OAI.UniversalTensorSquare.degreeTree43_421All`, `OAI.UniversalTensorSquare.degreeTree43_423All`, `OAI.UniversalTensorSquare.degreeTree43_47All`, `OAI.UniversalTensorSquare.degreeTree43_489All`, `OAI.UniversalTensorSquare.degreeTree43_57All`, `OAI.UniversalTensorSquare.degreeTree43_593All`, `OAI.UniversalTensorSquare.sg1348`, `OAI.UniversalTensorSquare.sg24300`, `OAI.UniversalTensorSquare.sg25812`, `OAI.UniversalTensorSquare.sg25815`, `OAI.UniversalTensorSquare.sg26017`, `OAI.UniversalTensorSquare.sg26593`, `OAI.UniversalTensorSquare.sg29458`, `OAI.UniversalTensorSquare.sg29648`, `OAI.UniversalTensorSquare.sg29850`, `OAI.UniversalTensorSquare.sg31312`, `OAI.UniversalTensorSquare.sg31336`, `OAI.UniversalTensorSquare.sg31340`, `OAI.UniversalTensorSquare.sg34706`, `OAI.UniversalTensorSquare.sg9850` and `OAI.UniversalTensorSquare.sg9862` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean (declaration OAI.UniversalTensorSquare.sg520)

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

lemma sg520 : RowSquare [4,1,1,1,1,1] [3,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
