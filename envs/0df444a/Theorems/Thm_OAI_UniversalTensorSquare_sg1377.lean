-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg1377
-- name    : OAI.UniversalTensorSquare.sg1377
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:15:16.157949+00:00
-- url     : https://prove2.me/theorems/25aef639-1006-4bcb-a583-efd959da690c
-- title:
--   OAI.UniversalTensorSquare.sg1377: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg1377` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg1377 : RowSquare [6,2,1,1,1] [3,3,2,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_237All`, `OAI.UniversalTensorSquare.degreeTree43_395All`, `OAI.UniversalTensorSquare.degreeTree43_459All`, `OAI.UniversalTensorSquare.degreeTree43_522All`, `OAI.UniversalTensorSquare.degreeTree43_536All`, `OAI.UniversalTensorSquare.degreeTree43_538All`, `OAI.UniversalTensorSquare.degreeTree43_600All`, `OAI.UniversalTensorSquare.sg22015`, `OAI.UniversalTensorSquare.sg22018`, `OAI.UniversalTensorSquare.sg24843`, `OAI.UniversalTensorSquare.sg24846`, `OAI.UniversalTensorSquare.sg26331`, `OAI.UniversalTensorSquare.sg26382`, `OAI.UniversalTensorSquare.sg26423`, `OAI.UniversalTensorSquare.sg26623`, `OAI.UniversalTensorSquare.sg26636`, `OAI.UniversalTensorSquare.sg26657`, `OAI.UniversalTensorSquare.sg26672`, `OAI.UniversalTensorSquare.sg26681`, `OAI.UniversalTensorSquare.sg26687`, `OAI.UniversalTensorSquare.sg26692`, `OAI.UniversalTensorSquare.sg26731`, `OAI.UniversalTensorSquare.sg26738`, `OAI.UniversalTensorSquare.sg27404`, `OAI.UniversalTensorSquare.sg29436`, `OAI.UniversalTensorSquare.sg29678`, `OAI.UniversalTensorSquare.sg29691`, `OAI.UniversalTensorSquare.sg30487`, `OAI.UniversalTensorSquare.sg30563`, `OAI.UniversalTensorSquare.sg31013`, `OAI.UniversalTensorSquare.sg31050`, `OAI.UniversalTensorSquare.sg31070`, `OAI.UniversalTensorSquare.sg31539`, `OAI.UniversalTensorSquare.sg31567`, `OAI.UniversalTensorSquare.sg7089`, `OAI.UniversalTensorSquare.sg9734`, `OAI.UniversalTensorSquare.sg9742`, `OAI.UniversalTensorSquare.sg9746`, `OAI.UniversalTensorSquare.sg9748` and `OAI.UniversalTensorSquare.sg9818` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean (declaration OAI.UniversalTensorSquare.sg1377)

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

lemma sg1377 : RowSquare [6,2,1,1,1] [3,3,2,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
