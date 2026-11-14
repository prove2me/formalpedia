-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg1032
-- name    : OAI.UniversalTensorSquare.sg1032
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-13T14:37:45.93861+00:00
-- url     : https://prove2.me/theorems/72e8d768-1413-4f4f-b219-4814774b8f3d
-- title:
--   OAI.UniversalTensorSquare.sg1032: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg1032` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg1032 : RowSquare [6,2,1,1] [2,2,2,2,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_201All`, `OAI.UniversalTensorSquare.degreeTree43_540All`, `OAI.UniversalTensorSquare.degreeTree43_630All`, `OAI.UniversalTensorSquare.degreeTree62_128All`, `OAI.UniversalTensorSquare.degreeTree62_210All`, `OAI.UniversalTensorSquare.degreeTree62_373All`, `OAI.UniversalTensorSquare.degreeTree62_42All`, `OAI.UniversalTensorSquare.degreeTree62_503All`, `OAI.UniversalTensorSquare.degreeTree62_599All`, `OAI.UniversalTensorSquare.degreeTree62_670All`, `OAI.UniversalTensorSquare.degreeTree62_674All`, `OAI.UniversalTensorSquare.degreeTree62_706All`, `OAI.UniversalTensorSquare.degreeTree62_715All`, `OAI.UniversalTensorSquare.degreeTree62_717All`, `OAI.UniversalTensorSquare.degreeTree62_829All`, `OAI.UniversalTensorSquare.degreeTree62_854All`, `OAI.UniversalTensorSquare.degreeTree62_909All`, `OAI.UniversalTensorSquare.degreeTree62_913All`, `OAI.UniversalTensorSquare.degreeTree62_947All`, `OAI.UniversalTensorSquare.sg21894`, `OAI.UniversalTensorSquare.sg25052` and `OAI.UniversalTensorSquare.sg9455` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean (declaration OAI.UniversalTensorSquare.sg1032)

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

lemma sg1032 : RowSquare [6,2,1,1] [2,2,2,2,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
