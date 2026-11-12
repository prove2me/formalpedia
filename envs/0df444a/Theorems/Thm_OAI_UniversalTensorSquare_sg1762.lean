-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg1762
-- name    : OAI.UniversalTensorSquare.sg1762
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:34:42.196252+00:00
-- url     : https://prove2.me/theorems/ca10dd4e-7fd2-4d20-b24c-e50d4dedb836
-- title:
--   OAI.UniversalTensorSquare.sg1762: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg1762` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg1762 : RowSquare [6,2,1,1,1,1] [3,2,2,2,2,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_390All`, `OAI.UniversalTensorSquare.degreeTree62_404All`, `OAI.UniversalTensorSquare.degreeTree62_476All`, `OAI.UniversalTensorSquare.degreeTree62_771All`, `OAI.UniversalTensorSquare.sg19115`, `OAI.UniversalTensorSquare.sg19715`, `OAI.UniversalTensorSquare.sg35822`, `OAI.UniversalTensorSquare.sg35824`, `OAI.UniversalTensorSquare.sg3584`, `OAI.UniversalTensorSquare.sg35844`, `OAI.UniversalTensorSquare.sg35846`, `OAI.UniversalTensorSquare.sg36654`, `OAI.UniversalTensorSquare.sg36656`, `OAI.UniversalTensorSquare.sg37124`, `OAI.UniversalTensorSquare.sg37126`, `OAI.UniversalTensorSquare.sg37270`, `OAI.UniversalTensorSquare.sg37273`, `OAI.UniversalTensorSquare.sg37276`, `OAI.UniversalTensorSquare.sg37278`, `OAI.UniversalTensorSquare.sg40915`, `OAI.UniversalTensorSquare.sg41601`, `OAI.UniversalTensorSquare.sg41681` and `OAI.UniversalTensorSquare.sg41754` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes3.lean (declaration OAI.UniversalTensorSquare.sg1762)

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

lemma sg1762 : RowSquare [6,2,1,1,1,1] [3,2,2,2,2,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
