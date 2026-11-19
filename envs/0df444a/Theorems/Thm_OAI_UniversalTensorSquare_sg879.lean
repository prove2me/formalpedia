-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg879
-- name    : OAI.UniversalTensorSquare.sg879
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T23:50:16.895992+00:00
-- url     : https://prove2.me/theorems/a80f6ecd-5c87-4ab5-8a7e-e9168ead6eed
-- title:
--   OAI.UniversalTensorSquare.sg879: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg879` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg879 : RowSquare [4,4,1,1] [2,2,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg13155`, `OAI.UniversalTensorSquare.sg14812`, `OAI.UniversalTensorSquare.sg20788`, `OAI.UniversalTensorSquare.sg22914`, `OAI.UniversalTensorSquare.sg24770`, `OAI.UniversalTensorSquare.sg25097`, `OAI.UniversalTensorSquare.sg25926`, `OAI.UniversalTensorSquare.sg26319`, `OAI.UniversalTensorSquare.sg27158`, `OAI.UniversalTensorSquare.sg27807`, `OAI.UniversalTensorSquare.sg27844`, `OAI.UniversalTensorSquare.sg28233`, `OAI.UniversalTensorSquare.sg28368`, `OAI.UniversalTensorSquare.sg28571`, `OAI.UniversalTensorSquare.sg29221`, `OAI.UniversalTensorSquare.sg29389`, `OAI.UniversalTensorSquare.sg29554`, `OAI.UniversalTensorSquare.sg30068`, `OAI.UniversalTensorSquare.sg30148` and `OAI.UniversalTensorSquare.sg30777` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean (declaration OAI.UniversalTensorSquare.sg879)

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

lemma sg879 : RowSquare [4,4,1,1] [2,2,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
