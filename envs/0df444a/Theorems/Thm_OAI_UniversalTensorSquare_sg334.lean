-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg334
-- name    : OAI.UniversalTensorSquare.sg334
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:22:35.886574+00:00
-- url     : https://prove2.me/theorems/17fdc96a-2875-4ee3-b7cf-3a6c89eb7767
-- title:
--   OAI.UniversalTensorSquare.sg334: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg334` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg334 : RowSquare [4,2,1,1] [2,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTreeAll43`, `OAI.UniversalTensorSquare.sg12178`, `OAI.UniversalTensorSquare.sg1631`, `OAI.UniversalTensorSquare.sg34278`, `OAI.UniversalTensorSquare.sg34304`, `OAI.UniversalTensorSquare.sg34489`, `OAI.UniversalTensorSquare.sg34536`, `OAI.UniversalTensorSquare.sg34947`, `OAI.UniversalTensorSquare.sg34972`, `OAI.UniversalTensorSquare.sg35262`, `OAI.UniversalTensorSquare.sg35264`, `OAI.UniversalTensorSquare.sg35266`, `OAI.UniversalTensorSquare.sg35269`, `OAI.UniversalTensorSquare.sg35271`, `OAI.UniversalTensorSquare.sg35329`, `OAI.UniversalTensorSquare.sg35331`, `OAI.UniversalTensorSquare.sg35393`, `OAI.UniversalTensorSquare.sg35431`, `OAI.UniversalTensorSquare.sg35455`, `OAI.UniversalTensorSquare.sg37527`, `OAI.UniversalTensorSquare.sg37533`, `OAI.UniversalTensorSquare.sg37534`, `OAI.UniversalTensorSquare.sg37544`, `OAI.UniversalTensorSquare.sg37557`, `OAI.UniversalTensorSquare.sg37560`, `OAI.UniversalTensorSquare.sg37572`, `OAI.UniversalTensorSquare.sg37573`, `OAI.UniversalTensorSquare.sg37574`, `OAI.UniversalTensorSquare.sg37591`, `OAI.UniversalTensorSquare.sg37603`, `OAI.UniversalTensorSquare.sg37604`, `OAI.UniversalTensorSquare.sg38209`, `OAI.UniversalTensorSquare.sg38787`, `OAI.UniversalTensorSquare.sg38794`, `OAI.UniversalTensorSquare.sg38795`, `OAI.UniversalTensorSquare.sg38810`, `OAI.UniversalTensorSquare.sg38821`, `OAI.UniversalTensorSquare.sg39387`, `OAI.UniversalTensorSquare.sg39399`, `OAI.UniversalTensorSquare.sg39877`, `OAI.UniversalTensorSquare.sg39884`, `OAI.UniversalTensorSquare.sg39897`, `OAI.UniversalTensorSquare.sg41437`, `OAI.UniversalTensorSquare.sg42151`, `OAI.UniversalTensorSquare.sg42154`, `OAI.UniversalTensorSquare.sg7453` and `OAI.UniversalTensorSquare.sg8167` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg334)

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

lemma sg334 : RowSquare [4,2,1,1] [2,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
