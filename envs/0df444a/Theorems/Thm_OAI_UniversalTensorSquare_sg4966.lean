-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg4966
-- name    : OAI.UniversalTensorSquare.sg4966
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:18:42.770518+00:00
-- url     : https://prove2.me/theorems/321dc684-a292-499d-8c8f-141ae1e13519
-- title:
--   OAI.UniversalTensorSquare.sg4966: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg4966` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes11.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes11.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg4966 : RowSquare [9,3,2,2,1] [3,2,2,2,2,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_311All`, `OAI.UniversalTensorSquare.degreeTree62_320All`, `OAI.UniversalTensorSquare.degreeTree62_329All`, `OAI.UniversalTensorSquare.degreeTree62_355All`, `OAI.UniversalTensorSquare.degreeTree62_393All`, `OAI.UniversalTensorSquare.degreeTree62_403All`, `OAI.UniversalTensorSquare.degreeTree62_743All`, `OAI.UniversalTensorSquare.degreeTree62_749All`, `OAI.UniversalTensorSquare.degreeTree62_797All`, `OAI.UniversalTensorSquare.degreeTree62_861All`, `OAI.UniversalTensorSquare.sg16165`, `OAI.UniversalTensorSquare.sg35501`, `OAI.UniversalTensorSquare.sg35507`, `OAI.UniversalTensorSquare.sg35509`, `OAI.UniversalTensorSquare.sg35526`, `OAI.UniversalTensorSquare.sg35557`, `OAI.UniversalTensorSquare.sg35723`, `OAI.UniversalTensorSquare.sg35762`, `OAI.UniversalTensorSquare.sg36625`, `OAI.UniversalTensorSquare.sg40241`, `OAI.UniversalTensorSquare.sg40244`, `OAI.UniversalTensorSquare.sg40245`, `OAI.UniversalTensorSquare.sg40276`, `OAI.UniversalTensorSquare.sg40298`, `OAI.UniversalTensorSquare.sg40525` and `OAI.UniversalTensorSquare.sg40824` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes11.lean (declaration OAI.UniversalTensorSquare.sg4966)

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

lemma sg4966 : RowSquare [9,3,2,2,1] [3,2,2,2,2,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
