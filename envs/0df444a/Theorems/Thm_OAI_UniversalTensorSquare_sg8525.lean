-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg8525
-- name    : OAI.UniversalTensorSquare.sg8525
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T23:44:26.746317+00:00
-- url     : https://prove2.me/theorems/412c97a5-8ff1-4539-97b0-f70b730da926
-- title:
--   OAI.UniversalTensorSquare.sg8525: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg8525` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg8525 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_12All`, `OAI.UniversalTensorSquare.sg24059`, `OAI.UniversalTensorSquare.sg24130`, `OAI.UniversalTensorSquare.sg24566`, `OAI.UniversalTensorSquare.sg24732`, `OAI.UniversalTensorSquare.sg24791`, `OAI.UniversalTensorSquare.sg24821`, `OAI.UniversalTensorSquare.sg25033`, `OAI.UniversalTensorSquare.sg25042`, `OAI.UniversalTensorSquare.sg25513`, `OAI.UniversalTensorSquare.sg25736`, `OAI.UniversalTensorSquare.sg26755` and `OAI.UniversalTensorSquare.sg28856` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean (declaration OAI.UniversalTensorSquare.sg8525)

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

lemma sg8525 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
