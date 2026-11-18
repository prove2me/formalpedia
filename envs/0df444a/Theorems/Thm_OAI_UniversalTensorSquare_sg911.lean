-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg911
-- name    : OAI.UniversalTensorSquare.sg911
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T23:56:02.551531+00:00
-- url     : https://prove2.me/theorems/a1e7f688-394b-46e9-a80a-36ef8b27101c
-- title:
--   OAI.UniversalTensorSquare.sg911: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg911` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg911 : RowSquare [5,2,1,1,1] [2,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_3All`, `OAI.UniversalTensorSquare.sg18973`, `OAI.UniversalTensorSquare.sg19904`, `OAI.UniversalTensorSquare.sg35555`, `OAI.UniversalTensorSquare.sg35716`, `OAI.UniversalTensorSquare.sg35718`, `OAI.UniversalTensorSquare.sg35771`, `OAI.UniversalTensorSquare.sg35902`, `OAI.UniversalTensorSquare.sg35904`, `OAI.UniversalTensorSquare.sg35908`, `OAI.UniversalTensorSquare.sg35914`, `OAI.UniversalTensorSquare.sg35979`, `OAI.UniversalTensorSquare.sg36367`, `OAI.UniversalTensorSquare.sg36369`, `OAI.UniversalTensorSquare.sg36412`, `OAI.UniversalTensorSquare.sg36414`, `OAI.UniversalTensorSquare.sg36428`, `OAI.UniversalTensorSquare.sg36633`, `OAI.UniversalTensorSquare.sg36649`, `OAI.UniversalTensorSquare.sg37721`, `OAI.UniversalTensorSquare.sg37723`, `OAI.UniversalTensorSquare.sg37727`, `OAI.UniversalTensorSquare.sg37777`, `OAI.UniversalTensorSquare.sg37979`, `OAI.UniversalTensorSquare.sg38102`, `OAI.UniversalTensorSquare.sg39235`, `OAI.UniversalTensorSquare.sg40400`, `OAI.UniversalTensorSquare.sg40402`, `OAI.UniversalTensorSquare.sg40403`, `OAI.UniversalTensorSquare.sg40786`, `OAI.UniversalTensorSquare.sg40788`, `OAI.UniversalTensorSquare.sg40789`, `OAI.UniversalTensorSquare.sg40829`, `OAI.UniversalTensorSquare.sg40946`, `OAI.UniversalTensorSquare.sg41514`, `OAI.UniversalTensorSquare.sg41541`, `OAI.UniversalTensorSquare.sg43083` and `OAI.UniversalTensorSquare.sg8985` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes1.lean (declaration OAI.UniversalTensorSquare.sg911)

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

lemma sg911 : RowSquare [5,2,1,1,1] [2,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
