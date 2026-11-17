-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg314
-- name    : OAI.UniversalTensorSquare.sg314
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T00:30:36.915899+00:00
-- url     : https://prove2.me/theorems/c98ef29d-93b2-40fb-b696-c7b719926c12
-- title:
--   OAI.UniversalTensorSquare.sg314: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg314` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg314 : RowSquare [4,1,1,1,1] [2,2,2,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_77All`, `OAI.UniversalTensorSquare.degreeTree43_128All`, `OAI.UniversalTensorSquare.degreeTree43_248All`, `OAI.UniversalTensorSquare.degreeTree43_398All`, `OAI.UniversalTensorSquare.degreeTree43_508All`, `OAI.UniversalTensorSquare.degreeTree43_59All`, `OAI.UniversalTensorSquare.degreeTree62_210All`, `OAI.UniversalTensorSquare.degreeTree62_212All`, `OAI.UniversalTensorSquare.degreeTree62_706All`, `OAI.UniversalTensorSquare.degreeTree62_947All`, `OAI.UniversalTensorSquare.sg15710`, `OAI.UniversalTensorSquare.sg23150`, `OAI.UniversalTensorSquare.sg23182`, `OAI.UniversalTensorSquare.sg24129`, `OAI.UniversalTensorSquare.sg24376`, `OAI.UniversalTensorSquare.sg24387`, `OAI.UniversalTensorSquare.sg24885`, `OAI.UniversalTensorSquare.sg24888`, `OAI.UniversalTensorSquare.sg24987`, `OAI.UniversalTensorSquare.sg25198`, `OAI.UniversalTensorSquare.sg25272`, `OAI.UniversalTensorSquare.sg26047`, `OAI.UniversalTensorSquare.sg26051`, `OAI.UniversalTensorSquare.sg26052`, `OAI.UniversalTensorSquare.sg26053`, `OAI.UniversalTensorSquare.sg26123`, `OAI.UniversalTensorSquare.sg26136`, `OAI.UniversalTensorSquare.sg26137`, `OAI.UniversalTensorSquare.sg26138`, `OAI.UniversalTensorSquare.sg26139`, `OAI.UniversalTensorSquare.sg26140`, `OAI.UniversalTensorSquare.sg26824`, `OAI.UniversalTensorSquare.sg26877`, `OAI.UniversalTensorSquare.sg26886`, `OAI.UniversalTensorSquare.sg26924`, `OAI.UniversalTensorSquare.sg26946`, `OAI.UniversalTensorSquare.sg26947`, `OAI.UniversalTensorSquare.sg27161`, `OAI.UniversalTensorSquare.sg27336`, `OAI.UniversalTensorSquare.sg27382`, `OAI.UniversalTensorSquare.sg27448`, `OAI.UniversalTensorSquare.sg27559`, `OAI.UniversalTensorSquare.sg27568`, `OAI.UniversalTensorSquare.sg27591`, `OAI.UniversalTensorSquare.sg27598`, `OAI.UniversalTensorSquare.sg28732`, `OAI.UniversalTensorSquare.sg28954`, `OAI.UniversalTensorSquare.sg28957`, `OAI.UniversalTensorSquare.sg29038`, `OAI.UniversalTensorSquare.sg29041`, `OAI.UniversalTensorSquare.sg29557`, `OAI.UniversalTensorSquare.sg29779` and `OAI.UniversalTensorSquare.sg29824` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean (declaration OAI.UniversalTensorSquare.sg314)

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

lemma sg314 : RowSquare [4,1,1,1,1] [2,2,2,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
