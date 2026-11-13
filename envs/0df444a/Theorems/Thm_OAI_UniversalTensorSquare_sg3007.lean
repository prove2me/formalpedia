-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg3007
-- name    : OAI.UniversalTensorSquare.sg3007
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T09:38:16.815715+00:00
-- url     : https://prove2.me/theorems/cfa459c4-3576-40fb-8c9e-e9c4eef73c95
-- title:
--   OAI.UniversalTensorSquare.sg3007: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg3007` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes6.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes6.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg3007 : RowSquare [8,3,2,1] [3,3,3,2,2,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_117All`, `OAI.UniversalTensorSquare.degreeTree62_120All`, `OAI.UniversalTensorSquare.degreeTree62_213All`, `OAI.UniversalTensorSquare.degreeTree62_263All`, `OAI.UniversalTensorSquare.degreeTree62_478All`, `OAI.UniversalTensorSquare.degreeTree62_491All`, `OAI.UniversalTensorSquare.degreeTree62_558All`, `OAI.UniversalTensorSquare.degreeTree62_664All`, `OAI.UniversalTensorSquare.degreeTree62_669All`, `OAI.UniversalTensorSquare.degreeTree62_707All`, `OAI.UniversalTensorSquare.degreeTree62_709All`, `OAI.UniversalTensorSquare.degreeTree62_713All`, `OAI.UniversalTensorSquare.degreeTree62_782All`, `OAI.UniversalTensorSquare.degreeTree62_98All`, `OAI.UniversalTensorSquare.sg32379`, `OAI.UniversalTensorSquare.sg33125`, `OAI.UniversalTensorSquare.sg33127`, `OAI.UniversalTensorSquare.sg33139`, `OAI.UniversalTensorSquare.sg33145`, `OAI.UniversalTensorSquare.sg33194`, `OAI.UniversalTensorSquare.sg33397`, `OAI.UniversalTensorSquare.sg33793`, `OAI.UniversalTensorSquare.sg34862`, `OAI.UniversalTensorSquare.sg34915`, `OAI.UniversalTensorSquare.sg35078`, `OAI.UniversalTensorSquare.sg35080`, `OAI.UniversalTensorSquare.sg38178`, `OAI.UniversalTensorSquare.sg38185`, `OAI.UniversalTensorSquare.sg40625`, `OAI.UniversalTensorSquare.sg40639` and `OAI.UniversalTensorSquare.sg42980` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes6.lean (declaration OAI.UniversalTensorSquare.sg3007)

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

lemma sg3007 : RowSquare [8,3,2,1] [3,3,3,2,2,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
