-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg2213
-- name    : OAI.UniversalTensorSquare.sg2213
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T22:31:32.708885+00:00
-- url     : https://prove2.me/theorems/0ca402a4-e573-469b-9708-05241e62deeb
-- title:
--   OAI.UniversalTensorSquare.sg2213: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg2213` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg2213 : RowSquare [6,4,3] [3,2,2,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_1003All`, `OAI.UniversalTensorSquare.degreeTree62_464All`, `OAI.UniversalTensorSquare.degreeTree62_990All`, `OAI.UniversalTensorSquare.degreeTree62_998All`, `OAI.UniversalTensorSquare.sg35713`, `OAI.UniversalTensorSquare.sg35715`, `OAI.UniversalTensorSquare.sg35717`, `OAI.UniversalTensorSquare.sg37089`, `OAI.UniversalTensorSquare.sg37163`, `OAI.UniversalTensorSquare.sg37718`, `OAI.UniversalTensorSquare.sg37720`, `OAI.UniversalTensorSquare.sg37722`, `OAI.UniversalTensorSquare.sg37994`, `OAI.UniversalTensorSquare.sg40956`, `OAI.UniversalTensorSquare.sg41269`, `OAI.UniversalTensorSquare.sg41338`, `OAI.UniversalTensorSquare.sg41649`, `OAI.UniversalTensorSquare.sg42957`, `OAI.UniversalTensorSquare.sg42960`, `OAI.UniversalTensorSquare.sg43096`, `OAI.UniversalTensorSquare.sg43152`, `OAI.UniversalTensorSquare.sg43154` and `OAI.UniversalTensorSquare.sg43162` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean (declaration OAI.UniversalTensorSquare.sg2213)

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

lemma sg2213 : RowSquare [6,4,3] [3,2,2,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
