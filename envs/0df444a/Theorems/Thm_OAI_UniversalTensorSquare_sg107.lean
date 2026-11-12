-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg107
-- name    : OAI.UniversalTensorSquare.sg107
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T20:32:32.592414+00:00
-- url     : https://prove2.me/theorems/e3fc56a2-d1cf-4c9e-931d-04cca43330db
-- title:
--   OAI.UniversalTensorSquare.sg107: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg107` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg107 : RowSquare [5,1] [6]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_374All`, `OAI.UniversalTensorSquare.sg20777`, `OAI.UniversalTensorSquare.sg21101`, `OAI.UniversalTensorSquare.sg21340`, `OAI.UniversalTensorSquare.sg21623`, `OAI.UniversalTensorSquare.sg22422`, `OAI.UniversalTensorSquare.sg27619`, `OAI.UniversalTensorSquare.sg27628`, `OAI.UniversalTensorSquare.sg27678`, `OAI.UniversalTensorSquare.sg27687`, `OAI.UniversalTensorSquare.sg27919`, `OAI.UniversalTensorSquare.sg28428` and `OAI.UniversalTensorSquare.sg29144` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg107)

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

lemma sg107 : RowSquare [5,1] [6] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
