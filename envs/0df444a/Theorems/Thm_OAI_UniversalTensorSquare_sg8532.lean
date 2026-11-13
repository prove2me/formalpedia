-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg8532
-- name    : OAI.UniversalTensorSquare.sg8532
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:49:07.570219+00:00
-- url     : https://prove2.me/theorems/f29d2563-21f1-4c23-a337-c471c36eb8b5
-- title:
--   OAI.UniversalTensorSquare.sg8532: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg8532` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg8532 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,2,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_159All`, `OAI.UniversalTensorSquare.degreeTree43_207All`, `OAI.UniversalTensorSquare.degreeTree43_27All`, `OAI.UniversalTensorSquare.degreeTree43_35All`, `OAI.UniversalTensorSquare.degreeTree43_37All`, `OAI.UniversalTensorSquare.degreeTree43_38All`, `OAI.UniversalTensorSquare.degreeTree43_457All`, `OAI.UniversalTensorSquare.sg23836`, `OAI.UniversalTensorSquare.sg23840`, `OAI.UniversalTensorSquare.sg25518`, `OAI.UniversalTensorSquare.sg25739`, `OAI.UniversalTensorSquare.sg25806`, `OAI.UniversalTensorSquare.sg26544` and `OAI.UniversalTensorSquare.sg28859` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean (declaration OAI.UniversalTensorSquare.sg8532)

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

lemma sg8532 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,2,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
