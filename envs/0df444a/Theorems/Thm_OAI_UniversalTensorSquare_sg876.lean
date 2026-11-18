-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg876
-- name    : OAI.UniversalTensorSquare.sg876
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T23:50:21.719344+00:00
-- url     : https://prove2.me/theorems/c5e2ab2c-9b2d-49f7-b6b5-682e88b9104e
-- title:
--   OAI.UniversalTensorSquare.sg876: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg876` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg876 : RowSquare [4,3,3] [3,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg35534`, `OAI.UniversalTensorSquare.sg35539`, `OAI.UniversalTensorSquare.sg35541`, `OAI.UniversalTensorSquare.sg35697`, `OAI.UniversalTensorSquare.sg35702`, `OAI.UniversalTensorSquare.sg35704`, `OAI.UniversalTensorSquare.sg40241`, `OAI.UniversalTensorSquare.sg40244`, `OAI.UniversalTensorSquare.sg40245`, `OAI.UniversalTensorSquare.sg40261`, `OAI.UniversalTensorSquare.sg40264` and `OAI.UniversalTensorSquare.sg40265` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean (declaration OAI.UniversalTensorSquare.sg876)

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

lemma sg876 : RowSquare [4,3,3] [3,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
