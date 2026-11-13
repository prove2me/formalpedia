-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg459
-- name    : OAI.UniversalTensorSquare.sg459
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:16:34.476945+00:00
-- url     : https://prove2.me/theorems/f4165996-aaf3-4450-858f-b6dbe56d2972
-- title:
--   OAI.UniversalTensorSquare.sg459: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg459` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg459 : RowSquare [3,2,1,1,1,1] [3,3,3]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_111All`, `OAI.UniversalTensorSquare.degreeTree43_248All`, `OAI.UniversalTensorSquare.degreeTree62_233All`, `OAI.UniversalTensorSquare.degreeTree62_304All`, `OAI.UniversalTensorSquare.degreeTree62_43All`, `OAI.UniversalTensorSquare.degreeTree62_583All`, `OAI.UniversalTensorSquare.degreeTree62_685All`, `OAI.UniversalTensorSquare.sg11862`, `OAI.UniversalTensorSquare.sg11987`, `OAI.UniversalTensorSquare.sg12048`, `OAI.UniversalTensorSquare.sg12175`, `OAI.UniversalTensorSquare.sg12691`, `OAI.UniversalTensorSquare.sg16676`, `OAI.UniversalTensorSquare.sg16687`, `OAI.UniversalTensorSquare.sg24222`, `OAI.UniversalTensorSquare.sg24789`, `OAI.UniversalTensorSquare.sg24817`, `OAI.UniversalTensorSquare.sg25101`, `OAI.UniversalTensorSquare.sg25111`, `OAI.UniversalTensorSquare.sg25123`, `OAI.UniversalTensorSquare.sg25124`, `OAI.UniversalTensorSquare.sg25135`, `OAI.UniversalTensorSquare.sg25138`, `OAI.UniversalTensorSquare.sg25148`, `OAI.UniversalTensorSquare.sg26793`, `OAI.UniversalTensorSquare.sg26798`, `OAI.UniversalTensorSquare.sg26801`, `OAI.UniversalTensorSquare.sg26811`, `OAI.UniversalTensorSquare.sg26818`, `OAI.UniversalTensorSquare.sg27503`, `OAI.UniversalTensorSquare.sg27543`, `OAI.UniversalTensorSquare.sg27578`, `OAI.UniversalTensorSquare.sg27581`, `OAI.UniversalTensorSquare.sg30629`, `OAI.UniversalTensorSquare.sg31111`, `OAI.UniversalTensorSquare.sg32009`, `OAI.UniversalTensorSquare.sg34614`, `OAI.UniversalTensorSquare.sg34620`, `OAI.UniversalTensorSquare.sg34691`, `OAI.UniversalTensorSquare.sg34692`, `OAI.UniversalTensorSquare.sg34705`, `OAI.UniversalTensorSquare.sg34711`, `OAI.UniversalTensorSquare.sg34712`, `OAI.UniversalTensorSquare.sg37077`, `OAI.UniversalTensorSquare.sg37082`, `OAI.UniversalTensorSquare.sg37084`, `OAI.UniversalTensorSquare.sg37983`, `OAI.UniversalTensorSquare.sg37988` and `OAI.UniversalTensorSquare.sg37990` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean (declaration OAI.UniversalTensorSquare.sg459)

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

lemma sg459 : RowSquare [3,2,1,1,1,1] [3,3,3] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
