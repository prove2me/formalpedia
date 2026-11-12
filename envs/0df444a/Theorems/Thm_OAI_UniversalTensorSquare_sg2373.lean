-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg2373
-- name    : OAI.UniversalTensorSquare.sg2373
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T01:23:10.267936+00:00
-- url     : https://prove2.me/theorems/5c4e3b6a-b823-4346-bab6-17bf791a79dd
-- title:
--   OAI.UniversalTensorSquare.sg2373: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg2373` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg2373 : RowSquare [8,2,1,1,1] [3,3,3,2,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_113All`, `OAI.UniversalTensorSquare.degreeTree62_114All`, `OAI.UniversalTensorSquare.degreeTree62_184All`, `OAI.UniversalTensorSquare.degreeTree62_196All`, `OAI.UniversalTensorSquare.degreeTree62_210All`, `OAI.UniversalTensorSquare.degreeTree62_212All`, `OAI.UniversalTensorSquare.degreeTree62_253All`, `OAI.UniversalTensorSquare.degreeTree62_256All`, `OAI.UniversalTensorSquare.degreeTree62_297All`, `OAI.UniversalTensorSquare.sg12565`, `OAI.UniversalTensorSquare.sg19725`, `OAI.UniversalTensorSquare.sg33255`, `OAI.UniversalTensorSquare.sg33256`, `OAI.UniversalTensorSquare.sg33258`, `OAI.UniversalTensorSquare.sg33259`, `OAI.UniversalTensorSquare.sg33287`, `OAI.UniversalTensorSquare.sg33291`, `OAI.UniversalTensorSquare.sg34191`, `OAI.UniversalTensorSquare.sg34289`, `OAI.UniversalTensorSquare.sg34290`, `OAI.UniversalTensorSquare.sg34292`, `OAI.UniversalTensorSquare.sg34293`, `OAI.UniversalTensorSquare.sg34295`, `OAI.UniversalTensorSquare.sg34297`, `OAI.UniversalTensorSquare.sg34336`, `OAI.UniversalTensorSquare.sg34340`, `OAI.UniversalTensorSquare.sg34342`, `OAI.UniversalTensorSquare.sg34362`, `OAI.UniversalTensorSquare.sg34364`, `OAI.UniversalTensorSquare.sg34366`, `OAI.UniversalTensorSquare.sg34368`, `OAI.UniversalTensorSquare.sg35161`, `OAI.UniversalTensorSquare.sg35173`, `OAI.UniversalTensorSquare.sg35321`, `OAI.UniversalTensorSquare.sg35343`, `OAI.UniversalTensorSquare.sg35357`, `OAI.UniversalTensorSquare.sg37346` and `OAI.UniversalTensorSquare.sg38651` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean (declaration OAI.UniversalTensorSquare.sg2373)

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

lemma sg2373 : RowSquare [8,2,1,1,1] [3,3,3,2,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
