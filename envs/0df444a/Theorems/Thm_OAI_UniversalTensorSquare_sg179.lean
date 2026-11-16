-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg179
-- name    : OAI.UniversalTensorSquare.sg179
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-16T02:42:57.566841+00:00
-- url     : https://prove2.me/theorems/5a507ab3-bbe4-4698-b043-d7ee2437b790
-- title:
--   OAI.UniversalTensorSquare.sg179: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg179` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg179 : RowSquare [4,1,1,1] [2,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg12716`, `OAI.UniversalTensorSquare.sg12717`, `OAI.UniversalTensorSquare.sg15748`, `OAI.UniversalTensorSquare.sg18035`, `OAI.UniversalTensorSquare.sg18036`, `OAI.UniversalTensorSquare.sg1893`, `OAI.UniversalTensorSquare.sg2046`, `OAI.UniversalTensorSquare.sg2048`, `OAI.UniversalTensorSquare.sg2050`, `OAI.UniversalTensorSquare.sg2061`, `OAI.UniversalTensorSquare.sg2063`, `OAI.UniversalTensorSquare.sg2064`, `OAI.UniversalTensorSquare.sg2547`, `OAI.UniversalTensorSquare.sg2550`, `OAI.UniversalTensorSquare.sg2551`, `OAI.UniversalTensorSquare.sg2552`, `OAI.UniversalTensorSquare.sg3704` and `OAI.UniversalTensorSquare.sg4504` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg179)

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

lemma sg179 : RowSquare [4,1,1,1] [2,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
