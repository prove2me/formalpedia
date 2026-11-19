-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg596
-- name    : OAI.UniversalTensorSquare.sg596
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T22:46:58.537682+00:00
-- url     : https://prove2.me/theorems/7590c885-3812-44ca-b564-24509efdb611
-- title:
--   OAI.UniversalTensorSquare.sg596: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg596` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg596 : RowSquare [5,1,1,1,1] [3,3,2,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_101All`, `OAI.UniversalTensorSquare.degreeTree43_207All`, `OAI.UniversalTensorSquare.degreeTree43_236All`, `OAI.UniversalTensorSquare.degreeTree43_555All`, `OAI.UniversalTensorSquare.degreeTree43_598All`, `OAI.UniversalTensorSquare.degreeTree62_542All`, `OAI.UniversalTensorSquare.sg24861`, `OAI.UniversalTensorSquare.sg24885`, `OAI.UniversalTensorSquare.sg24901`, `OAI.UniversalTensorSquare.sg27329`, `OAI.UniversalTensorSquare.sg29404`, `OAI.UniversalTensorSquare.sg29410`, `OAI.UniversalTensorSquare.sg30308`, `OAI.UniversalTensorSquare.sg30474`, `OAI.UniversalTensorSquare.sg30505`, `OAI.UniversalTensorSquare.sg31294`, `OAI.UniversalTensorSquare.sg31561`, `OAI.UniversalTensorSquare.sg36692`, `OAI.UniversalTensorSquare.sg36694`, `OAI.UniversalTensorSquare.sg36695`, `OAI.UniversalTensorSquare.sg38451`, `OAI.UniversalTensorSquare.sg39615`, `OAI.UniversalTensorSquare.sg40425` and `OAI.UniversalTensorSquare.sg6225` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean (declaration OAI.UniversalTensorSquare.sg596)

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

lemma sg596 : RowSquare [5,1,1,1,1] [3,3,2,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
