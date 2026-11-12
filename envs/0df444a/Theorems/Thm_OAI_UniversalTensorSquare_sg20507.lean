-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg20507
-- name    : OAI.UniversalTensorSquare.sg20507
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:51:20.625818+00:00
-- url     : https://prove2.me/theorems/b5707707-05cd-4b9d-8d0f-b79215bc287f
-- title:
--   OAI.UniversalTensorSquare.sg20507: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg20507` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg20507 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,2,2,2,2,2,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_146All`, `OAI.UniversalTensorSquare.degreeTree62_152All`, `OAI.UniversalTensorSquare.degreeTree62_163All`, `OAI.UniversalTensorSquare.degreeTree62_165All`, `OAI.UniversalTensorSquare.degreeTree62_166All`, `OAI.UniversalTensorSquare.degreeTree62_168All`, `OAI.UniversalTensorSquare.degreeTree62_174All`, `OAI.UniversalTensorSquare.degreeTree62_183All`, `OAI.UniversalTensorSquare.degreeTree62_193All`, `OAI.UniversalTensorSquare.degreeTree62_195All`, `OAI.UniversalTensorSquare.degreeTree62_199All`, `OAI.UniversalTensorSquare.degreeTree62_207All`, `OAI.UniversalTensorSquare.degreeTree62_209All`, `OAI.UniversalTensorSquare.degreeTree62_210All`, `OAI.UniversalTensorSquare.degreeTree62_212All`, `OAI.UniversalTensorSquare.degreeTree62_220All`, `OAI.UniversalTensorSquare.degreeTree62_225All`, `OAI.UniversalTensorSquare.degreeTree62_226All`, `OAI.UniversalTensorSquare.degreeTree62_227All`, `OAI.UniversalTensorSquare.degreeTree62_339All`, `OAI.UniversalTensorSquare.degreeTree62_349All`, `OAI.UniversalTensorSquare.degreeTree62_393All`, `OAI.UniversalTensorSquare.degreeTree62_413All`, `OAI.UniversalTensorSquare.degreeTree62_427All`, `OAI.UniversalTensorSquare.degreeTree62_434All`, `OAI.UniversalTensorSquare.degreeTree62_449All`, `OAI.UniversalTensorSquare.degreeTree62_475All`, `OAI.UniversalTensorSquare.degreeTree62_519All`, `OAI.UniversalTensorSquare.degreeTree62_522All`, `OAI.UniversalTensorSquare.degreeTree62_533All`, `OAI.UniversalTensorSquare.degreeTree62_534All`, `OAI.UniversalTensorSquare.degreeTree62_542All`, `OAI.UniversalTensorSquare.degreeTree62_557All`, `OAI.UniversalTensorSquare.degreeTree62_562All`, `OAI.UniversalTensorSquare.degreeTree62_574All`, `OAI.UniversalTensorSquare.degreeTree62_621All`, `OAI.UniversalTensorSquare.degreeTree62_625All`, `OAI.UniversalTensorSquare.degreeTree62_627All`, `OAI.UniversalTensorSquare.degreeTree62_630All`, `OAI.UniversalTensorSquare.degreeTree62_640All`, `OAI.UniversalTensorSquare.degreeTree62_645All`, `OAI.UniversalTensorSquare.degreeTree62_654All`, `OAI.UniversalTensorSquare.degreeTree62_662All`, `OAI.UniversalTensorSquare.degreeTree62_85All`, `OAI.UniversalTensorSquare.degreeTree62_91All`, `OAI.UniversalTensorSquare.degreeTree62_94All`, `OAI.UniversalTensorSquare.sg32180`, `OAI.UniversalTensorSquare.sg32193`, `OAI.UniversalTensorSquare.sg32239`, `OAI.UniversalTensorSquare.sg32918`, `OAI.UniversalTensorSquare.sg33641`, `OAI.UniversalTensorSquare.sg33713`, `OAI.UniversalTensorSquare.sg33768`, `OAI.UniversalTensorSquare.sg33935`, `OAI.UniversalTensorSquare.sg34038`, `OAI.UniversalTensorSquare.sg34051`, `OAI.UniversalTensorSquare.sg34133`, `OAI.UniversalTensorSquare.sg35771`, `OAI.UniversalTensorSquare.sg36428`, `OAI.UniversalTensorSquare.sg36474`, `OAI.UniversalTensorSquare.sg36754`, `OAI.UniversalTensorSquare.sg36898`, `OAI.UniversalTensorSquare.sg37054`, `OAI.UniversalTensorSquare.sg38043`, `OAI.UniversalTensorSquare.sg38103`, `OAI.UniversalTensorSquare.sg38222`, `OAI.UniversalTensorSquare.sg38243`, `OAI.UniversalTensorSquare.sg38363`, `OAI.UniversalTensorSquare.sg38442`, `OAI.UniversalTensorSquare.sg38496`, `OAI.UniversalTensorSquare.sg38516`, `OAI.UniversalTensorSquare.sg38596`, `OAI.UniversalTensorSquare.sg38629`, `OAI.UniversalTensorSquare.sg38695`, `OAI.UniversalTensorSquare.sg38726`, `OAI.UniversalTensorSquare.sg38753`, `OAI.UniversalTensorSquare.sg38778`, `OAI.UniversalTensorSquare.sg38848`, `OAI.UniversalTensorSquare.sg39093`, `OAI.UniversalTensorSquare.sg39284`, `OAI.UniversalTensorSquare.sg39406` and `OAI.UniversalTensorSquare.sg39577` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean (declaration OAI.UniversalTensorSquare.sg20507)

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

lemma sg20507 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,2,2,2,2,2,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
