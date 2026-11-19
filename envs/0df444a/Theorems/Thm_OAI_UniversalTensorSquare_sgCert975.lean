-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert975
-- name    : OAI.UniversalTensorSquare.sgCert975
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:47:45.360853+00:00
-- url     : https://prove2.me/theorems/c2375875-db1c-42aa-8d42-d9bb0ada562d
-- title:
--   OAI.UniversalTensorSquare.sgCert975: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert975` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert975 : solveCompact 10 (.full [7,3]) (.full [3,3,2,1,1]) (.full [3,3,2,1,1])
--       (certificateEdges [3,3,2,1,1] [3,3,2,1,1] [7,3] (Equiv.refl (Fin 10)) sgB975 sgT975) sgFlag975 = 6
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB975` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgFlag975` and `OAI.UniversalTensorSquare.sgT975` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg16442`, `OAI.UniversalTensorSquare.sg16479`, `OAI.UniversalTensorSquare.sg16565`, `OAI.UniversalTensorSquare.sg17827`, `OAI.UniversalTensorSquare.sg33293`, `OAI.UniversalTensorSquare.sg34841`, `OAI.UniversalTensorSquare.sg36702`, `OAI.UniversalTensorSquare.sg37316`, `OAI.UniversalTensorSquare.sg38611`, `OAI.UniversalTensorSquare.sg39191`, `OAI.UniversalTensorSquare.sg39194`, `OAI.UniversalTensorSquare.sg39196`, `OAI.UniversalTensorSquare.sg39539`, `OAI.UniversalTensorSquare.sg39553`, `OAI.UniversalTensorSquare.sg39555`, `OAI.UniversalTensorSquare.sg39556`, `OAI.UniversalTensorSquare.sg39739`, `OAI.UniversalTensorSquare.sg40061`, `OAI.UniversalTensorSquare.sg40063`, `OAI.UniversalTensorSquare.sg40064`, `OAI.UniversalTensorSquare.sg41266`, `OAI.UniversalTensorSquare.sg41292`, `OAI.UniversalTensorSquare.sg41295`, `OAI.UniversalTensorSquare.sg41314`, `OAI.UniversalTensorSquare.sg41319`, `OAI.UniversalTensorSquare.sg41335`, `OAI.UniversalTensorSquare.sg41354`, `OAI.UniversalTensorSquare.sg41357`, `OAI.UniversalTensorSquare.sg41376`, `OAI.UniversalTensorSquare.sg41713`, `OAI.UniversalTensorSquare.sg41738`, `OAI.UniversalTensorSquare.sg41895`, `OAI.UniversalTensorSquare.sg41896`, `OAI.UniversalTensorSquare.sg41944`, `OAI.UniversalTensorSquare.sg41966`, `OAI.UniversalTensorSquare.sg41976`, `OAI.UniversalTensorSquare.sg42255`, `OAI.UniversalTensorSquare.sg42270`, `OAI.UniversalTensorSquare.sg42378`, `OAI.UniversalTensorSquare.sg42393`, `OAI.UniversalTensorSquare.sg42456`, `OAI.UniversalTensorSquare.sg42959`, `OAI.UniversalTensorSquare.sg43109`, `OAI.UniversalTensorSquare.sg43151`, `OAI.UniversalTensorSquare.sg43163`, `OAI.UniversalTensorSquare.sg43176`, `OAI.UniversalTensorSquare.sg43228`, `OAI.UniversalTensorSquare.sg8049`, `OAI.UniversalTensorSquare.sg8073` and `OAI.UniversalTensorSquare.sg975` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean (declaration OAI.UniversalTensorSquare.sgCert975)

import Mathlib
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US006

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

lemma sgCert975 : solveCompact 10 (.full [7,3]) (.full [3,3,2,1,1]) (.full [3,3,2,1,1])
    (certificateEdges [3,3,2,1,1] [3,3,2,1,1] [7,3] (Equiv.refl (Fin 10)) sgB975 sgT975) sgFlag975 = 6 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
