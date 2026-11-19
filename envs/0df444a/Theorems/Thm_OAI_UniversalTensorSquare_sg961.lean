-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg961
-- name    : OAI.UniversalTensorSquare.sg961
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T00:05:06.051192+00:00
-- url     : https://prove2.me/theorems/12a6865c-a8f9-4383-83a6-8ec64f97dd26
-- title:
--   OAI.UniversalTensorSquare.sg961: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg961` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg961 : RowSquare [5,3,1,1] [2,2,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_112All`, `OAI.UniversalTensorSquare.degreeTree43_77All`, `OAI.UniversalTensorSquare.degreeTree43_97All`, `OAI.UniversalTensorSquare.degreeTree62_102All`, `OAI.UniversalTensorSquare.degreeTree62_37All`, `OAI.UniversalTensorSquare.degreeTree62_454All`, `OAI.UniversalTensorSquare.degreeTree62_56All`, `OAI.UniversalTensorSquare.degreeTree62_59All`, `OAI.UniversalTensorSquare.degreeTree62_67All`, `OAI.UniversalTensorSquare.degreeTree62_80All`, `OAI.UniversalTensorSquare.degreeTree62_91All`, `OAI.UniversalTensorSquare.sg17527`, `OAI.UniversalTensorSquare.sg17609`, `OAI.UniversalTensorSquare.sg17926`, `OAI.UniversalTensorSquare.sg23645`, `OAI.UniversalTensorSquare.sg23650`, `OAI.UniversalTensorSquare.sg23651`, `OAI.UniversalTensorSquare.sg23660`, `OAI.UniversalTensorSquare.sg23738`, `OAI.UniversalTensorSquare.sg24189`, `OAI.UniversalTensorSquare.sg32407`, `OAI.UniversalTensorSquare.sg32409`, `OAI.UniversalTensorSquare.sg32417`, `OAI.UniversalTensorSquare.sg33028`, `OAI.UniversalTensorSquare.sg33030`, `OAI.UniversalTensorSquare.sg33647`, `OAI.UniversalTensorSquare.sg3655`, `OAI.UniversalTensorSquare.sg37111`, `OAI.UniversalTensorSquare.sg37113`, `OAI.UniversalTensorSquare.sg37115`, `OAI.UniversalTensorSquare.sg37680`, `OAI.UniversalTensorSquare.sg39508`, `OAI.UniversalTensorSquare.sg40581`, `OAI.UniversalTensorSquare.sg40583`, `OAI.UniversalTensorSquare.sg40584`, `OAI.UniversalTensorSquare.sg40969`, `OAI.UniversalTensorSquare.sg40971`, `OAI.UniversalTensorSquare.sg40972`, `OAI.UniversalTensorSquare.sg41559`, `OAI.UniversalTensorSquare.sg41561`, `OAI.UniversalTensorSquare.sg42105`, `OAI.UniversalTensorSquare.sg42164`, `OAI.UniversalTensorSquare.sg42274`, `OAI.UniversalTensorSquare.sg42275`, `OAI.UniversalTensorSquare.sg42276`, `OAI.UniversalTensorSquare.sg42579`, `OAI.UniversalTensorSquare.sg42831`, `OAI.UniversalTensorSquare.sg9425` and `OAI.UniversalTensorSquare.sg9493` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean (declaration OAI.UniversalTensorSquare.sg961)

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

lemma sg961 : RowSquare [5,3,1,1] [2,2,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
