-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg8418
-- name    : OAI.UniversalTensorSquare.sg8418
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T23:38:58.875768+00:00
-- url     : https://prove2.me/theorems/34ce4c28-dfa7-4ae0-a234-79cdbdd53c24
-- title:
--   OAI.UniversalTensorSquare.sg8418: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg8418` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg8418 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_164All`, `OAI.UniversalTensorSquare.degreeTree43_205All`, `OAI.UniversalTensorSquare.degreeTree43_28All`, `OAI.UniversalTensorSquare.degreeTree43_33All`, `OAI.UniversalTensorSquare.degreeTree43_35All`, `OAI.UniversalTensorSquare.degreeTree43_441All`, `OAI.UniversalTensorSquare.degreeTree43_457All`, `OAI.UniversalTensorSquare.degreeTree43_496All`, `OAI.UniversalTensorSquare.sg25379`, `OAI.UniversalTensorSquare.sg25391`, `OAI.UniversalTensorSquare.sg25415`, `OAI.UniversalTensorSquare.sg25455`, `OAI.UniversalTensorSquare.sg25537`, `OAI.UniversalTensorSquare.sg25637`, `OAI.UniversalTensorSquare.sg25754`, `OAI.UniversalTensorSquare.sg25770`, `OAI.UniversalTensorSquare.sg26213`, `OAI.UniversalTensorSquare.sg28281`, `OAI.UniversalTensorSquare.sg28619`, `OAI.UniversalTensorSquare.sg28746`, `OAI.UniversalTensorSquare.sg28751`, `OAI.UniversalTensorSquare.sg28807`, `OAI.UniversalTensorSquare.sg28839`, `OAI.UniversalTensorSquare.sg28969`, `OAI.UniversalTensorSquare.sg29045` and `OAI.UniversalTensorSquare.sg29114` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean (declaration OAI.UniversalTensorSquare.sg8418)

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

lemma sg8418 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
