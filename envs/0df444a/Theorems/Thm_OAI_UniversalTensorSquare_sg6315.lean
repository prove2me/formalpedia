-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg6315
-- name    : OAI.UniversalTensorSquare.sg6315
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:25:04.173008+00:00
-- url     : https://prove2.me/theorems/fa1b0a69-5190-483b-b1f8-5d00a7c27a9b
-- title:
--   OAI.UniversalTensorSquare.sg6315: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg6315` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes14.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes14.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg6315 : RowSquare [5,5,2,2,1,1,1,1,1] [4,4,4,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_29All`, `OAI.UniversalTensorSquare.sg21985`, `OAI.UniversalTensorSquare.sg21997`, `OAI.UniversalTensorSquare.sg22040`, `OAI.UniversalTensorSquare.sg22043`, `OAI.UniversalTensorSquare.sg22046`, `OAI.UniversalTensorSquare.sg22052`, `OAI.UniversalTensorSquare.sg22057`, `OAI.UniversalTensorSquare.sg22066`, `OAI.UniversalTensorSquare.sg22309`, `OAI.UniversalTensorSquare.sg22310`, `OAI.UniversalTensorSquare.sg22386`, `OAI.UniversalTensorSquare.sg22400`, `OAI.UniversalTensorSquare.sg22406`, `OAI.UniversalTensorSquare.sg22411`, `OAI.UniversalTensorSquare.sg22412`, `OAI.UniversalTensorSquare.sg23500`, `OAI.UniversalTensorSquare.sg23502` and `OAI.UniversalTensorSquare.sg23519` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes14.lean (declaration OAI.UniversalTensorSquare.sg6315)

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

lemma sg6315 : RowSquare [5,5,2,2,1,1,1,1,1] [4,4,4,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
