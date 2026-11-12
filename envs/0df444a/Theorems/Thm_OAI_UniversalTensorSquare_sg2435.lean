-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg2435
-- name    : OAI.UniversalTensorSquare.sg2435
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T02:07:22.612023+00:00
-- url     : https://prove2.me/theorems/86486761-2315-486f-89df-43b4e0437b05
-- title:
--   OAI.UniversalTensorSquare.sg2435: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg2435` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg2435 : RowSquare [8,3,2] [4,3,2,2,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_445All`, `OAI.UniversalTensorSquare.degreeTree62_887All`, `OAI.UniversalTensorSquare.sg17836`, `OAI.UniversalTensorSquare.sg38282`, `OAI.UniversalTensorSquare.sg38699`, `OAI.UniversalTensorSquare.sg41037`, `OAI.UniversalTensorSquare.sg41944`, `OAI.UniversalTensorSquare.sg43074` and `OAI.UniversalTensorSquare.sg43109` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean (declaration OAI.UniversalTensorSquare.sg2435)

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

lemma sg2435 : RowSquare [8,3,2] [4,3,2,2,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
