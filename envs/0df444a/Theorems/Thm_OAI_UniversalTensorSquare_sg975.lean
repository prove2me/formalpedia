-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg975
-- name    : OAI.UniversalTensorSquare.sg975
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-18T00:08:18.797376+00:00
-- url     : https://prove2.me/theorems/fce6b654-55c0-4457-8f40-97dc42d2ff2c
-- title:
--   OAI.UniversalTensorSquare.sg975: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg975` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg975 : RowSquare [5,3,2] [2,2,2,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_31All`, `OAI.UniversalTensorSquare.degreeTree62_32All`, `OAI.UniversalTensorSquare.degreeTree62_597All`, `OAI.UniversalTensorSquare.degreeTree62_601All`, `OAI.UniversalTensorSquare.degreeTree62_692All`, `OAI.UniversalTensorSquare.degreeTree62_699All`, `OAI.UniversalTensorSquare.sg16321`, `OAI.UniversalTensorSquare.sg16341`, `OAI.UniversalTensorSquare.sg16364`, `OAI.UniversalTensorSquare.sg16442`, `OAI.UniversalTensorSquare.sg16479`, `OAI.UniversalTensorSquare.sg16565`, `OAI.UniversalTensorSquare.sg16594`, `OAI.UniversalTensorSquare.sg16600`, `OAI.UniversalTensorSquare.sg16605`, `OAI.UniversalTensorSquare.sg17827`, `OAI.UniversalTensorSquare.sg34822`, `OAI.UniversalTensorSquare.sg34841`, `OAI.UniversalTensorSquare.sg36702`, `OAI.UniversalTensorSquare.sg36771`, `OAI.UniversalTensorSquare.sg37279`, `OAI.UniversalTensorSquare.sg37316`, `OAI.UniversalTensorSquare.sg37325`, `OAI.UniversalTensorSquare.sg37383`, `OAI.UniversalTensorSquare.sg37413`, `OAI.UniversalTensorSquare.sg38057`, `OAI.UniversalTensorSquare.sg38169`, `OAI.UniversalTensorSquare.sg38561`, `OAI.UniversalTensorSquare.sg38590`, `OAI.UniversalTensorSquare.sg38611`, `OAI.UniversalTensorSquare.sg38648`, `OAI.UniversalTensorSquare.sg38655`, `OAI.UniversalTensorSquare.sg38689`, `OAI.UniversalTensorSquare.sg39191`, `OAI.UniversalTensorSquare.sg39194`, `OAI.UniversalTensorSquare.sg39196`, `OAI.UniversalTensorSquare.sg39319`, `OAI.UniversalTensorSquare.sg39325`, `OAI.UniversalTensorSquare.sg39369`, `OAI.UniversalTensorSquare.sg39539`, `OAI.UniversalTensorSquare.sg39553`, `OAI.UniversalTensorSquare.sg39555`, `OAI.UniversalTensorSquare.sg39556`, `OAI.UniversalTensorSquare.sg39610`, `OAI.UniversalTensorSquare.sg39739`, `OAI.UniversalTensorSquare.sg39794`, `OAI.UniversalTensorSquare.sg40061`, `OAI.UniversalTensorSquare.sg40063`, `OAI.UniversalTensorSquare.sg40064`, `OAI.UniversalTensorSquare.sg40613`, `OAI.UniversalTensorSquare.sg40636`, `OAI.UniversalTensorSquare.sg40994`, `OAI.UniversalTensorSquare.sg41037`, `OAI.UniversalTensorSquare.sg41238`, `OAI.UniversalTensorSquare.sg41266`, `OAI.UniversalTensorSquare.sg41282`, `OAI.UniversalTensorSquare.sg41292`, `OAI.UniversalTensorSquare.sg41295`, `OAI.UniversalTensorSquare.sg41296`, `OAI.UniversalTensorSquare.sg41306`, `OAI.UniversalTensorSquare.sg41314`, `OAI.UniversalTensorSquare.sg41319`, `OAI.UniversalTensorSquare.sg41335`, `OAI.UniversalTensorSquare.sg41351`, `OAI.UniversalTensorSquare.sg41354`, `OAI.UniversalTensorSquare.sg41357`, `OAI.UniversalTensorSquare.sg41358`, `OAI.UniversalTensorSquare.sg41368`, `OAI.UniversalTensorSquare.sg41376`, `OAI.UniversalTensorSquare.sg41713`, `OAI.UniversalTensorSquare.sg41738`, `OAI.UniversalTensorSquare.sg41748`, `OAI.UniversalTensorSquare.sg41895`, `OAI.UniversalTensorSquare.sg41896`, `OAI.UniversalTensorSquare.sg41920`, `OAI.UniversalTensorSquare.sg41944`, `OAI.UniversalTensorSquare.sg41966`, `OAI.UniversalTensorSquare.sg41976`, `OAI.UniversalTensorSquare.sg41977`, `OAI.UniversalTensorSquare.sg41985`, `OAI.UniversalTensorSquare.sg42123`, `OAI.UniversalTensorSquare.sg42207`, `OAI.UniversalTensorSquare.sg42255`, `OAI.UniversalTensorSquare.sg42270`, `OAI.UniversalTensorSquare.sg42271`, `OAI.UniversalTensorSquare.sg42277`, `OAI.UniversalTensorSquare.sg42378`, `OAI.UniversalTensorSquare.sg42393`, `OAI.UniversalTensorSquare.sg42400`, `OAI.UniversalTensorSquare.sg42456`, `OAI.UniversalTensorSquare.sg42587`, `OAI.UniversalTensorSquare.sg42946`, `OAI.UniversalTensorSquare.sg42959`, `OAI.UniversalTensorSquare.sg42969`, `OAI.UniversalTensorSquare.sg42979`, `OAI.UniversalTensorSquare.sg43109`, `OAI.UniversalTensorSquare.sg43151`, `OAI.UniversalTensorSquare.sg43163`, `OAI.UniversalTensorSquare.sg43176`, `OAI.UniversalTensorSquare.sg43228`, `OAI.UniversalTensorSquare.sg8049` and `OAI.UniversalTensorSquare.sg8073` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean (declaration OAI.UniversalTensorSquare.sg975)

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

lemma sg975 : RowSquare [5,3,2] [2,2,2,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
