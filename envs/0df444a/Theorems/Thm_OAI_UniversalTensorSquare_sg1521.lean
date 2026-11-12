-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg1521
-- name    : OAI.UniversalTensorSquare.sg1521
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:20:30.130222+00:00
-- url     : https://prove2.me/theorems/80a87716-2cef-443c-a058-20d2dd662fc6
-- title:
--   OAI.UniversalTensorSquare.sg1521: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg1521` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg1521 : RowSquare [7,2,1,1] [3,3,2,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_533All`, `OAI.UniversalTensorSquare.degreeTree43_587All`, `OAI.UniversalTensorSquare.degreeTree62_584All`, `OAI.UniversalTensorSquare.degreeTree62_602All`, `OAI.UniversalTensorSquare.degreeTree62_690All`, `OAI.UniversalTensorSquare.degreeTree62_694All`, `OAI.UniversalTensorSquare.degreeTree62_707All`, `OAI.UniversalTensorSquare.degreeTree62_897All`, `OAI.UniversalTensorSquare.degreeTree62_900All`, `OAI.UniversalTensorSquare.degreeTree62_943All`, `OAI.UniversalTensorSquare.sg22004`, `OAI.UniversalTensorSquare.sg24958`, `OAI.UniversalTensorSquare.sg25468`, `OAI.UniversalTensorSquare.sg26401`, `OAI.UniversalTensorSquare.sg26638`, `OAI.UniversalTensorSquare.sg26683`, `OAI.UniversalTensorSquare.sg26694`, `OAI.UniversalTensorSquare.sg27460`, `OAI.UniversalTensorSquare.sg27543`, `OAI.UniversalTensorSquare.sg30158`, `OAI.UniversalTensorSquare.sg30787`, `OAI.UniversalTensorSquare.sg31011`, `OAI.UniversalTensorSquare.sg31272`, `OAI.UniversalTensorSquare.sg31394`, `OAI.UniversalTensorSquare.sg31493`, `OAI.UniversalTensorSquare.sg38438`, `OAI.UniversalTensorSquare.sg38457`, `OAI.UniversalTensorSquare.sg38460`, `OAI.UniversalTensorSquare.sg38462`, `OAI.UniversalTensorSquare.sg38550`, `OAI.UniversalTensorSquare.sg39232`, `OAI.UniversalTensorSquare.sg39249`, `OAI.UniversalTensorSquare.sg39252`, `OAI.UniversalTensorSquare.sg39254`, `OAI.UniversalTensorSquare.sg39545`, `OAI.UniversalTensorSquare.sg39623`, `OAI.UniversalTensorSquare.sg39682`, `OAI.UniversalTensorSquare.sg39683`, `OAI.UniversalTensorSquare.sg39685`, `OAI.UniversalTensorSquare.sg39686`, `OAI.UniversalTensorSquare.sg40093`, `OAI.UniversalTensorSquare.sg40108`, `OAI.UniversalTensorSquare.sg40111`, `OAI.UniversalTensorSquare.sg40112`, `OAI.UniversalTensorSquare.sg41753`, `OAI.UniversalTensorSquare.sg41916`, `OAI.UniversalTensorSquare.sg42262`, `OAI.UniversalTensorSquare.sg42263`, `OAI.UniversalTensorSquare.sg42264`, `OAI.UniversalTensorSquare.sg42397`, `OAI.UniversalTensorSquare.sg42398`, `OAI.UniversalTensorSquare.sg42399` and `OAI.UniversalTensorSquare.sg9859` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes2.lean (declaration OAI.UniversalTensorSquare.sg1521)

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

lemma sg1521 : RowSquare [7,2,1,1] [3,3,2,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
