-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg1177
-- name    : OAI.UniversalTensorSquare.sg1177
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T20:38:36.057906+00:00
-- url     : https://prove2.me/theorems/441b7fee-b1d2-4011-931a-f40cfc9077a6
-- title:
--   OAI.UniversalTensorSquare.sg1177: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg1177` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg1177 : RowSquare [3,3,1,1,1,1,1] [11]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree24_1All`, `OAI.UniversalTensorSquare.degreeTree43_315All`, `OAI.UniversalTensorSquare.degreeTree43_316All`, `OAI.UniversalTensorSquare.degreeTree43_333All`, `OAI.UniversalTensorSquare.degreeTree43_340All`, `OAI.UniversalTensorSquare.degreeTree43_371All`, `OAI.UniversalTensorSquare.degreeTree43_372All`, `OAI.UniversalTensorSquare.sg10869`, `OAI.UniversalTensorSquare.sg12975`, `OAI.UniversalTensorSquare.sg15606`, `OAI.UniversalTensorSquare.sg20974`, `OAI.UniversalTensorSquare.sg20981`, `OAI.UniversalTensorSquare.sg27711`, `OAI.UniversalTensorSquare.sg27761`, `OAI.UniversalTensorSquare.sg27769`, `OAI.UniversalTensorSquare.sg27809`, `OAI.UniversalTensorSquare.sg27951`, `OAI.UniversalTensorSquare.sg28649` and `OAI.UniversalTensorSquare.sg29226` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg1177)

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

lemma sg1177 : RowSquare [3,3,1,1,1,1,1] [11] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
