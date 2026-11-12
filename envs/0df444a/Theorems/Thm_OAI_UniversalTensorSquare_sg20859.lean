-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg20859
-- name    : OAI.UniversalTensorSquare.sg20859
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:56:50.595956+00:00
-- url     : https://prove2.me/theorems/32e9c965-e427-4f84-8a8e-5240d0aa9ac2
-- title:
--   OAI.UniversalTensorSquare.sg20859: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg20859` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes50.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes50.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg20859 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,2,2,2,2,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_322All`, `OAI.UniversalTensorSquare.degreeTree62_323All`, `OAI.UniversalTensorSquare.degreeTree62_388All`, `OAI.UniversalTensorSquare.degreeTree62_471All`, `OAI.UniversalTensorSquare.degreeTree62_483All`, `OAI.UniversalTensorSquare.degreeTree62_515All`, `OAI.UniversalTensorSquare.degreeTree62_752All`, `OAI.UniversalTensorSquare.sg35917`, `OAI.UniversalTensorSquare.sg35964`, `OAI.UniversalTensorSquare.sg36062`, `OAI.UniversalTensorSquare.sg36172`, `OAI.UniversalTensorSquare.sg36211`, `OAI.UniversalTensorSquare.sg37073`, `OAI.UniversalTensorSquare.sg37141`, `OAI.UniversalTensorSquare.sg37207`, `OAI.UniversalTensorSquare.sg37307`, `OAI.UniversalTensorSquare.sg37337`, `OAI.UniversalTensorSquare.sg37451`, `OAI.UniversalTensorSquare.sg37492`, `OAI.UniversalTensorSquare.sg37533`, `OAI.UniversalTensorSquare.sg37608`, `OAI.UniversalTensorSquare.sg37643`, `OAI.UniversalTensorSquare.sg37673`, `OAI.UniversalTensorSquare.sg40280`, `OAI.UniversalTensorSquare.sg40358`, `OAI.UniversalTensorSquare.sg40530`, `OAI.UniversalTensorSquare.sg40600`, `OAI.UniversalTensorSquare.sg40621`, `OAI.UniversalTensorSquare.sg40683`, `OAI.UniversalTensorSquare.sg40713`, `OAI.UniversalTensorSquare.sg40744`, `OAI.UniversalTensorSquare.sg40776`, `OAI.UniversalTensorSquare.sg41226`, `OAI.UniversalTensorSquare.sg41258`, `OAI.UniversalTensorSquare.sg41270`, `OAI.UniversalTensorSquare.sg41317`, `OAI.UniversalTensorSquare.sg41339`, `OAI.UniversalTensorSquare.sg41379`, `OAI.UniversalTensorSquare.sg41397`, `OAI.UniversalTensorSquare.sg41411`, `OAI.UniversalTensorSquare.sg41425`, `OAI.UniversalTensorSquare.sg41469`, `OAI.UniversalTensorSquare.sg41482` and `OAI.UniversalTensorSquare.sg41492` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes50.lean (declaration OAI.UniversalTensorSquare.sg20859)

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

lemma sg20859 : RowSquare [10,9,2,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,2,2,2,2,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
