-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg8468
-- name    : OAI.UniversalTensorSquare.sg8468
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:47:47.933487+00:00
-- url     : https://prove2.me/theorems/9ed5836d-4628-45aa-83df-87472963830d
-- title:
--   OAI.UniversalTensorSquare.sg8468: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg8468` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg8468 : RowSquare [6,4,3,2,1,1,1,1,1,1] [5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_309All`, `OAI.UniversalTensorSquare.degreeTree43_314All`, `OAI.UniversalTensorSquare.degreeTree43_320All`, `OAI.UniversalTensorSquare.degreeTree43_327All`, `OAI.UniversalTensorSquare.degreeTree43_340All`, `OAI.UniversalTensorSquare.degreeTree43_342All`, `OAI.UniversalTensorSquare.degreeTree43_343All`, `OAI.UniversalTensorSquare.degreeTree43_347All`, `OAI.UniversalTensorSquare.degreeTree43_353All`, `OAI.UniversalTensorSquare.degreeTree43_356All`, `OAI.UniversalTensorSquare.degreeTree43_358All`, `OAI.UniversalTensorSquare.degreeTree43_361All`, `OAI.UniversalTensorSquare.degreeTree43_366All`, `OAI.UniversalTensorSquare.degreeTree43_369All`, `OAI.UniversalTensorSquare.degreeTree43_372All`, `OAI.UniversalTensorSquare.degreeTree43_377All`, `OAI.UniversalTensorSquare.degreeTree43_378All`, `OAI.UniversalTensorSquare.degreeTree43_380All`, `OAI.UniversalTensorSquare.degreeTree43_382All`, `OAI.UniversalTensorSquare.degreeTree43_384All`, `OAI.UniversalTensorSquare.degreeTree43_390All`, `OAI.UniversalTensorSquare.degreeTree43_392All`, `OAI.UniversalTensorSquare.degreeTree43_394All`, `OAI.UniversalTensorSquare.degreeTree43_397All`, `OAI.UniversalTensorSquare.degreeTree43_399All`, `OAI.UniversalTensorSquare.degreeTree43_485All`, `OAI.UniversalTensorSquare.degreeTree43_621All`, `OAI.UniversalTensorSquare.degreeTree43_635All`, `OAI.UniversalTensorSquare.degreeTree43_637All`, `OAI.UniversalTensorSquare.degreeTree43_640All`, `OAI.UniversalTensorSquare.degreeTree43_642All`, `OAI.UniversalTensorSquare.sg27728`, `OAI.UniversalTensorSquare.sg27780`, `OAI.UniversalTensorSquare.sg27821`, `OAI.UniversalTensorSquare.sg27849`, `OAI.UniversalTensorSquare.sg27856`, `OAI.UniversalTensorSquare.sg27955`, `OAI.UniversalTensorSquare.sg27962`, `OAI.UniversalTensorSquare.sg28004`, `OAI.UniversalTensorSquare.sg28012`, `OAI.UniversalTensorSquare.sg28041`, `OAI.UniversalTensorSquare.sg28494` and `OAI.UniversalTensorSquare.sg31916` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean (declaration OAI.UniversalTensorSquare.sg8468)

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

lemma sg8468 : RowSquare [6,4,3,2,1,1,1,1,1,1] [5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
