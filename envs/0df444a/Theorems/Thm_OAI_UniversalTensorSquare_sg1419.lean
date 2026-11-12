-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg1419
-- name    : OAI.UniversalTensorSquare.sg1419
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:17:37.668232+00:00
-- url     : https://prove2.me/theorems/a63151e9-f550-424b-bcc0-961474b9a71e
-- title:
--   OAI.UniversalTensorSquare.sg1419: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg1419` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg1419 : RowSquare [6,3,1,1] [3,2,2,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_461All`, `OAI.UniversalTensorSquare.degreeTree62_462All`, `OAI.UniversalTensorSquare.degreeTree62_578All`, `OAI.UniversalTensorSquare.degreeTree62_581All`, `OAI.UniversalTensorSquare.sg23717`, `OAI.UniversalTensorSquare.sg24277`, `OAI.UniversalTensorSquare.sg25573`, `OAI.UniversalTensorSquare.sg25574`, `OAI.UniversalTensorSquare.sg26084`, `OAI.UniversalTensorSquare.sg37076`, `OAI.UniversalTensorSquare.sg37078` and `OAI.UniversalTensorSquare.sg37080` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean (declaration OAI.UniversalTensorSquare.sg1419)

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

lemma sg1419 : RowSquare [6,3,1,1] [3,2,2,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
