-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg20518
-- name    : OAI.UniversalTensorSquare.sg20518
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:51:30.032537+00:00
-- url     : https://prove2.me/theorems/1847afb3-8c23-4868-b3c8-7ded9335f1cc
-- title:
--   OAI.UniversalTensorSquare.sg20518: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg20518` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg20518 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,3,2,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_117All`, `OAI.UniversalTensorSquare.degreeTree62_12All`, `OAI.UniversalTensorSquare.degreeTree62_131All`, `OAI.UniversalTensorSquare.degreeTree62_136All`, `OAI.UniversalTensorSquare.degreeTree62_137All`, `OAI.UniversalTensorSquare.degreeTree62_138All`, `OAI.UniversalTensorSquare.degreeTree62_168All`, `OAI.UniversalTensorSquare.degreeTree62_16All`, `OAI.UniversalTensorSquare.degreeTree62_170All`, `OAI.UniversalTensorSquare.degreeTree62_173All`, `OAI.UniversalTensorSquare.degreeTree62_176All`, `OAI.UniversalTensorSquare.degreeTree62_198All`, `OAI.UniversalTensorSquare.degreeTree62_213All`, `OAI.UniversalTensorSquare.degreeTree62_225All`, `OAI.UniversalTensorSquare.degreeTree62_226All`, `OAI.UniversalTensorSquare.degreeTree62_229All`, `OAI.UniversalTensorSquare.degreeTree62_230All`, `OAI.UniversalTensorSquare.degreeTree62_277All`, `OAI.UniversalTensorSquare.degreeTree62_287All`, `OAI.UniversalTensorSquare.degreeTree62_290All`, `OAI.UniversalTensorSquare.degreeTree62_291All`, `OAI.UniversalTensorSquare.degreeTree62_297All`, `OAI.UniversalTensorSquare.degreeTree62_298All`, `OAI.UniversalTensorSquare.degreeTree62_306All`, `OAI.UniversalTensorSquare.degreeTree62_307All`, `OAI.UniversalTensorSquare.degreeTree62_310All`, `OAI.UniversalTensorSquare.degreeTree62_35All`, `OAI.UniversalTensorSquare.degreeTree62_3All`, `OAI.UniversalTensorSquare.degreeTree62_46All`, `OAI.UniversalTensorSquare.degreeTree62_49All`, `OAI.UniversalTensorSquare.degreeTree62_512All`, `OAI.UniversalTensorSquare.degreeTree62_610All`, `OAI.UniversalTensorSquare.degreeTree62_621All`, `OAI.UniversalTensorSquare.degreeTree62_65All`, `OAI.UniversalTensorSquare.degreeTree62_677All`, `OAI.UniversalTensorSquare.degreeTree62_67All`, `OAI.UniversalTensorSquare.degreeTree62_709All`, `OAI.UniversalTensorSquare.degreeTree62_719All`, `OAI.UniversalTensorSquare.degreeTree62_722All`, `OAI.UniversalTensorSquare.degreeTree62_72All`, `OAI.UniversalTensorSquare.degreeTree62_746All`, `OAI.UniversalTensorSquare.degreeTree62_851All`, `OAI.UniversalTensorSquare.degreeTree62_860All`, `OAI.UniversalTensorSquare.degreeTree62_87All`, `OAI.UniversalTensorSquare.degreeTree62_937All`, `OAI.UniversalTensorSquare.degreeTree62_953All`, `OAI.UniversalTensorSquare.degreeTreeAll62`, `OAI.UniversalTensorSquare.sg32199`, `OAI.UniversalTensorSquare.sg32629`, `OAI.UniversalTensorSquare.sg32636`, `OAI.UniversalTensorSquare.sg32660`, `OAI.UniversalTensorSquare.sg32666`, `OAI.UniversalTensorSquare.sg32689`, `OAI.UniversalTensorSquare.sg32805`, `OAI.UniversalTensorSquare.sg33042`, `OAI.UniversalTensorSquare.sg33386`, `OAI.UniversalTensorSquare.sg33521`, `OAI.UniversalTensorSquare.sg33592`, `OAI.UniversalTensorSquare.sg33617`, `OAI.UniversalTensorSquare.sg33748`, `OAI.UniversalTensorSquare.sg33979`, `OAI.UniversalTensorSquare.sg34383`, `OAI.UniversalTensorSquare.sg34431`, `OAI.UniversalTensorSquare.sg35051`, `OAI.UniversalTensorSquare.sg37687`, `OAI.UniversalTensorSquare.sg38902`, `OAI.UniversalTensorSquare.sg41496`, `OAI.UniversalTensorSquare.sg42021`, `OAI.UniversalTensorSquare.sg42072`, `OAI.UniversalTensorSquare.sg42079`, `OAI.UniversalTensorSquare.sg42084`, `OAI.UniversalTensorSquare.sg42502`, `OAI.UniversalTensorSquare.sg42539`, `OAI.UniversalTensorSquare.sg42544`, `OAI.UniversalTensorSquare.sg42547`, `OAI.UniversalTensorSquare.sg42766` and `OAI.UniversalTensorSquare.sg42768` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean (declaration OAI.UniversalTensorSquare.sg20518)

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

lemma sg20518 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,3,2,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
