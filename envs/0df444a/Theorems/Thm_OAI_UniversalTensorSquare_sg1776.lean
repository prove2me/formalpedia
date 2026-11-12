-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg1776
-- name    : OAI.UniversalTensorSquare.sg1776
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:36:01.315142+00:00
-- url     : https://prove2.me/theorems/e828aef7-23c4-4dad-9334-dbd86c377bd5
-- title:
--   OAI.UniversalTensorSquare.sg1776: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg1776` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg1776 : RowSquare [6,3,1,1,1] [3,2,2,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_144All`, `OAI.UniversalTensorSquare.degreeTree43_358All`, `OAI.UniversalTensorSquare.degreeTree43_362All`, `OAI.UniversalTensorSquare.degreeTree43_413All`, `OAI.UniversalTensorSquare.degreeTree43_459All`, `OAI.UniversalTensorSquare.sg24310`, `OAI.UniversalTensorSquare.sg25395`, `OAI.UniversalTensorSquare.sg25539`, `OAI.UniversalTensorSquare.sg25556`, `OAI.UniversalTensorSquare.sg25557`, `OAI.UniversalTensorSquare.sg25568`, `OAI.UniversalTensorSquare.sg25569`, `OAI.UniversalTensorSquare.sg25941`, `OAI.UniversalTensorSquare.sg25973`, `OAI.UniversalTensorSquare.sg25983`, `OAI.UniversalTensorSquare.sg26338`, `OAI.UniversalTensorSquare.sg26582`, `OAI.UniversalTensorSquare.sg28284`, `OAI.UniversalTensorSquare.sg28901` and `OAI.UniversalTensorSquare.sg30796` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes3.lean (declaration OAI.UniversalTensorSquare.sg1776)

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

lemma sg1776 : RowSquare [6,3,1,1,1] [3,2,2,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
