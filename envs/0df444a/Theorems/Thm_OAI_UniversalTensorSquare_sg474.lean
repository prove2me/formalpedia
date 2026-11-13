-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg474
-- name    : OAI.UniversalTensorSquare.sg474
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:17:09.418976+00:00
-- url     : https://prove2.me/theorems/cde71f85-cf22-4ca7-ac8b-90fa6d43a317
-- title:
--   OAI.UniversalTensorSquare.sg474: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg474` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg474 : RowSquare [3,2,1,1,1,1] [9]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree24_12All`, `OAI.UniversalTensorSquare.degreeTree24_19All`, `OAI.UniversalTensorSquare.degreeTree24_1All`, `OAI.UniversalTensorSquare.degreeTree26_0All`, `OAI.UniversalTensorSquare.degreeTree26_18All`, `OAI.UniversalTensorSquare.degreeTree26_21All`, `OAI.UniversalTensorSquare.degreeTree26_24All`, `OAI.UniversalTensorSquare.degreeTree26_41All`, `OAI.UniversalTensorSquare.degreeTree26_53All`, `OAI.UniversalTensorSquare.degreeTree39_50All`, `OAI.UniversalTensorSquare.degreeTree39_54All`, `OAI.UniversalTensorSquare.degreeTree39_63All`, `OAI.UniversalTensorSquare.degreeTree39_81All`, `OAI.UniversalTensorSquare.degreeTree43_291All`, `OAI.UniversalTensorSquare.degreeTree43_357All`, `OAI.UniversalTensorSquare.degreeTree43_361All`, `OAI.UniversalTensorSquare.degreeTree43_380All`, `OAI.UniversalTensorSquare.degreeTree43_435All`, `OAI.UniversalTensorSquare.degreeTree43_441All`, `OAI.UniversalTensorSquare.degreeTree43_498All`, `OAI.UniversalTensorSquare.sg13125`, `OAI.UniversalTensorSquare.sg13172`, `OAI.UniversalTensorSquare.sg13213`, `OAI.UniversalTensorSquare.sg13434`, `OAI.UniversalTensorSquare.sg15525`, `OAI.UniversalTensorSquare.sg15533`, `OAI.UniversalTensorSquare.sg15535`, `OAI.UniversalTensorSquare.sg15545`, `OAI.UniversalTensorSquare.sg23592`, `OAI.UniversalTensorSquare.sg24767`, `OAI.UniversalTensorSquare.sg25928`, `OAI.UniversalTensorSquare.sg25955`, `OAI.UniversalTensorSquare.sg25960`, `OAI.UniversalTensorSquare.sg26327`, `OAI.UniversalTensorSquare.sg26353`, `OAI.UniversalTensorSquare.sg26564`, `OAI.UniversalTensorSquare.sg26569`, `OAI.UniversalTensorSquare.sg27155`, `OAI.UniversalTensorSquare.sg28260`, `OAI.UniversalTensorSquare.sg28299`, `OAI.UniversalTensorSquare.sg28640`, `OAI.UniversalTensorSquare.sg28679`, `OAI.UniversalTensorSquare.sg28876`, `OAI.UniversalTensorSquare.sg28884`, `OAI.UniversalTensorSquare.sg28890`, `OAI.UniversalTensorSquare.sg28925`, `OAI.UniversalTensorSquare.sg29217`, `OAI.UniversalTensorSquare.sg29264`, `OAI.UniversalTensorSquare.sg29339`, `OAI.UniversalTensorSquare.sg29562`, `OAI.UniversalTensorSquare.sg29978`, `OAI.UniversalTensorSquare.sg30018`, `OAI.UniversalTensorSquare.sg30070`, `OAI.UniversalTensorSquare.sg30134`, `OAI.UniversalTensorSquare.sg30150`, `OAI.UniversalTensorSquare.sg30716`, `OAI.UniversalTensorSquare.sg30785` and `OAI.UniversalTensorSquare.sg31173` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg474)

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

lemma sg474 : RowSquare [3,2,1,1,1,1] [9] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
