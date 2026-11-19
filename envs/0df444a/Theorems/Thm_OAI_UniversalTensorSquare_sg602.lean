-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg602
-- name    : OAI.UniversalTensorSquare.sg602
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T22:49:28.576437+00:00
-- url     : https://prove2.me/theorems/d9ddbcc3-6e84-4928-a50b-742db3161f2a
-- title:
--   OAI.UniversalTensorSquare.sg602: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg602` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg602 : RowSquare [5,1,1,1,1] [4,4,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_508All`, `OAI.UniversalTensorSquare.degreeTree43_511All`, `OAI.UniversalTensorSquare.degreeTree43_555All`, `OAI.UniversalTensorSquare.degreeTree43_587All`, `OAI.UniversalTensorSquare.degreeTree43_598All`, `OAI.UniversalTensorSquare.degreeTree43_633All`, `OAI.UniversalTensorSquare.sg27161`, `OAI.UniversalTensorSquare.sg27186`, `OAI.UniversalTensorSquare.sg27213`, `OAI.UniversalTensorSquare.sg27232`, `OAI.UniversalTensorSquare.sg27336`, `OAI.UniversalTensorSquare.sg27358`, `OAI.UniversalTensorSquare.sg27382`, `OAI.UniversalTensorSquare.sg27398`, `OAI.UniversalTensorSquare.sg29235`, `OAI.UniversalTensorSquare.sg31180`, `OAI.UniversalTensorSquare.sg31252`, `OAI.UniversalTensorSquare.sg31346`, `OAI.UniversalTensorSquare.sg35585` and `OAI.UniversalTensorSquare.sg6276` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean (declaration OAI.UniversalTensorSquare.sg602)

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

lemma sg602 : RowSquare [5,1,1,1,1] [4,4,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
