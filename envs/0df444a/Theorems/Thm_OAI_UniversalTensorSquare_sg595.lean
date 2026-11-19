-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg595
-- name    : OAI.UniversalTensorSquare.sg595
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T22:46:27.828834+00:00
-- url     : https://prove2.me/theorems/85fefcd0-fc6d-4837-a5b8-cea6a18fb882
-- title:
--   OAI.UniversalTensorSquare.sg595: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg595` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg595 : RowSquare [5,1,1,1,1] [3,3,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_324All`, `OAI.UniversalTensorSquare.degreeTree43_385All`, `OAI.UniversalTensorSquare.degreeTree43_551All`, `OAI.UniversalTensorSquare.degreeTree43_555All`, `OAI.UniversalTensorSquare.degreeTree43_593All`, `OAI.UniversalTensorSquare.degreeTree43_614All`, `OAI.UniversalTensorSquare.degreeTree43_75All`, `OAI.UniversalTensorSquare.degreeTree62_673All`, `OAI.UniversalTensorSquare.degreeTreeAll41`, `OAI.UniversalTensorSquare.sg23639`, `OAI.UniversalTensorSquare.sg26541`, `OAI.UniversalTensorSquare.sg27079`, `OAI.UniversalTensorSquare.sg27301`, `OAI.UniversalTensorSquare.sg29303`, `OAI.UniversalTensorSquare.sg29309`, `OAI.UniversalTensorSquare.sg29510`, `OAI.UniversalTensorSquare.sg29513`, `OAI.UniversalTensorSquare.sg31145`, `OAI.UniversalTensorSquare.sg31233`, `OAI.UniversalTensorSquare.sg31338`, `OAI.UniversalTensorSquare.sg31554`, `OAI.UniversalTensorSquare.sg38252`, `OAI.UniversalTensorSquare.sg39062`, `OAI.UniversalTensorSquare.sg39362`, `OAI.UniversalTensorSquare.sg42667`, `OAI.UniversalTensorSquare.sg6222`, `OAI.UniversalTensorSquare.sg6230` and `OAI.UniversalTensorSquare.sg7526` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean (declaration OAI.UniversalTensorSquare.sg595)

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

lemma sg595 : RowSquare [5,1,1,1,1] [3,3,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
