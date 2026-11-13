-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg2752
-- name    : OAI.UniversalTensorSquare.sg2752
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T06:32:38.7713+00:00
-- url     : https://prove2.me/theorems/68455061-dbb2-4e9c-a67a-dcabad50e11d
-- title:
--   OAI.UniversalTensorSquare.sg2752: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg2752` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg2752 : RowSquare [7,3,2,1,1] [4,2,2,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_326All`, `OAI.UniversalTensorSquare.degreeTree62_349All`, `OAI.UniversalTensorSquare.degreeTree62_361All`, `OAI.UniversalTensorSquare.degreeTree62_367All`, `OAI.UniversalTensorSquare.degreeTree62_394All`, `OAI.UniversalTensorSquare.degreeTree62_430All`, `OAI.UniversalTensorSquare.degreeTree62_773All`, `OAI.UniversalTensorSquare.degreeTree62_782All`, `OAI.UniversalTensorSquare.degreeTree62_786All`, `OAI.UniversalTensorSquare.degreeTree62_821All`, `OAI.UniversalTensorSquare.degreeTree62_844All`, `OAI.UniversalTensorSquare.degreeTree62_851All`, `OAI.UniversalTensorSquare.degreeTree62_852All`, `OAI.UniversalTensorSquare.degreeTree62_857All`, `OAI.UniversalTensorSquare.sg18402`, `OAI.UniversalTensorSquare.sg31982`, `OAI.UniversalTensorSquare.sg31983`, `OAI.UniversalTensorSquare.sg31996`, `OAI.UniversalTensorSquare.sg36298`, `OAI.UniversalTensorSquare.sg36519`, `OAI.UniversalTensorSquare.sg40362`, `OAI.UniversalTensorSquare.sg40650`, `OAI.UniversalTensorSquare.sg40766`, `OAI.UniversalTensorSquare.sg40769`, `OAI.UniversalTensorSquare.sg40771`, `OAI.UniversalTensorSquare.sg41178`, `OAI.UniversalTensorSquare.sg41496` and `OAI.UniversalTensorSquare.sg41503` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes5.lean (declaration OAI.UniversalTensorSquare.sg2752)

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

lemma sg2752 : RowSquare [7,3,2,1,1] [4,2,2,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
