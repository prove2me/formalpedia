-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg3636
-- name    : OAI.UniversalTensorSquare.sg3636
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T16:00:07.054732+00:00
-- url     : https://prove2.me/theorems/fd6f249a-1ce8-4f7f-8f02-6700ae400791
-- title:
--   OAI.UniversalTensorSquare.sg3636: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg3636` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg3636 : RowSquare [8,3,2,2] [3,3,3,2,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_483All`, `OAI.UniversalTensorSquare.sg15936`, `OAI.UniversalTensorSquare.sg33207`, `OAI.UniversalTensorSquare.sg34085`, `OAI.UniversalTensorSquare.sg34105`, `OAI.UniversalTensorSquare.sg34284`, `OAI.UniversalTensorSquare.sg34787`, `OAI.UniversalTensorSquare.sg34807`, `OAI.UniversalTensorSquare.sg34952`, `OAI.UniversalTensorSquare.sg35116`, `OAI.UniversalTensorSquare.sg35983`, `OAI.UniversalTensorSquare.sg36704`, `OAI.UniversalTensorSquare.sg36723`, `OAI.UniversalTensorSquare.sg37093`, `OAI.UniversalTensorSquare.sg37167`, `OAI.UniversalTensorSquare.sg37414`, `OAI.UniversalTensorSquare.sg38065`, `OAI.UniversalTensorSquare.sg38405`, `OAI.UniversalTensorSquare.sg38477`, `OAI.UniversalTensorSquare.sg38494`, `OAI.UniversalTensorSquare.sg38661`, `OAI.UniversalTensorSquare.sg39282`, `OAI.UniversalTensorSquare.sg39575`, `OAI.UniversalTensorSquare.sg39755`, `OAI.UniversalTensorSquare.sg40571`, `OAI.UniversalTensorSquare.sg40582`, `OAI.UniversalTensorSquare.sg40959`, `OAI.UniversalTensorSquare.sg40999`, `OAI.UniversalTensorSquare.sg41203`, `OAI.UniversalTensorSquare.sg41245`, `OAI.UniversalTensorSquare.sg41359`, `OAI.UniversalTensorSquare.sg41552`, `OAI.UniversalTensorSquare.sg41662`, `OAI.UniversalTensorSquare.sg41859`, `OAI.UniversalTensorSquare.sg41968`, `OAI.UniversalTensorSquare.sg42127`, `OAI.UniversalTensorSquare.sg42216` and `OAI.UniversalTensorSquare.sg42223` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean (declaration OAI.UniversalTensorSquare.sg3636)

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

lemma sg3636 : RowSquare [8,3,2,2] [3,3,3,2,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
