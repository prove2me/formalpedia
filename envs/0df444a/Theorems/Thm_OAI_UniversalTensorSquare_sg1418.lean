-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg1418
-- name    : OAI.UniversalTensorSquare.sg1418
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:17:42.405201+00:00
-- url     : https://prove2.me/theorems/d4734cca-b503-4d7e-91ba-59b73841dcc5
-- title:
--   OAI.UniversalTensorSquare.sg1418: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg1418` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg1418 : RowSquare [6,3,1,1] [3,2,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_526All`, `OAI.UniversalTensorSquare.degreeTree62_529All`, `OAI.UniversalTensorSquare.degreeTree62_627All`, `OAI.UniversalTensorSquare.degreeTree62_629All`, `OAI.UniversalTensorSquare.degreeTree62_631All`, `OAI.UniversalTensorSquare.degreeTree62_801All`, `OAI.UniversalTensorSquare.degreeTree62_865All`, `OAI.UniversalTensorSquare.degreeTree62_915All`, `OAI.UniversalTensorSquare.sg18417`, `OAI.UniversalTensorSquare.sg18567`, `OAI.UniversalTensorSquare.sg18724`, `OAI.UniversalTensorSquare.sg25730`, `OAI.UniversalTensorSquare.sg35792`, `OAI.UniversalTensorSquare.sg35795`, `OAI.UniversalTensorSquare.sg35797`, `OAI.UniversalTensorSquare.sg38940`, `OAI.UniversalTensorSquare.sg38944`, `OAI.UniversalTensorSquare.sg38946`, `OAI.UniversalTensorSquare.sg40415`, `OAI.UniversalTensorSquare.sg40418`, `OAI.UniversalTensorSquare.sg40419`, `OAI.UniversalTensorSquare.sg40441`, `OAI.UniversalTensorSquare.sg40444`, `OAI.UniversalTensorSquare.sg40445`, `OAI.UniversalTensorSquare.sg40801`, `OAI.UniversalTensorSquare.sg40804`, `OAI.UniversalTensorSquare.sg40805`, `OAI.UniversalTensorSquare.sg40812`, `OAI.UniversalTensorSquare.sg40814` and `OAI.UniversalTensorSquare.sg40815` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean (declaration OAI.UniversalTensorSquare.sg1418)

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

lemma sg1418 : RowSquare [6,3,1,1] [3,2,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
