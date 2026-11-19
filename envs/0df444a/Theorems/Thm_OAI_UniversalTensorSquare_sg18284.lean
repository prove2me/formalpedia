-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg18284
-- name    : OAI.UniversalTensorSquare.sg18284
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:10:34.896316+00:00
-- url     : https://prove2.me/theorems/f4e78c6d-5e1c-4505-a6ab-8109f1778e3a
-- title:
--   OAI.UniversalTensorSquare.sg18284: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg18284` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes44.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes44.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg18284 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [4,4,3,3,3,3,2,2,2,2,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_574All`, `OAI.UniversalTensorSquare.sg33640`, `OAI.UniversalTensorSquare.sg33653`, `OAI.UniversalTensorSquare.sg33934`, `OAI.UniversalTensorSquare.sg33969`, `OAI.UniversalTensorSquare.sg34087`, `OAI.UniversalTensorSquare.sg34248`, `OAI.UniversalTensorSquare.sg34483`, `OAI.UniversalTensorSquare.sg34508`, `OAI.UniversalTensorSquare.sg34533`, `OAI.UniversalTensorSquare.sg37053`, `OAI.UniversalTensorSquare.sg38595`, `OAI.UniversalTensorSquare.sg39374`, `OAI.UniversalTensorSquare.sg40046`, `OAI.UniversalTensorSquare.sg40180`, `OAI.UniversalTensorSquare.sg40211`, `OAI.UniversalTensorSquare.sg40220`, `OAI.UniversalTensorSquare.sg41158` and `OAI.UniversalTensorSquare.sg41179` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes44.lean (declaration OAI.UniversalTensorSquare.sg18284)

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

lemma sg18284 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [4,4,3,3,3,3,2,2,2,2,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
