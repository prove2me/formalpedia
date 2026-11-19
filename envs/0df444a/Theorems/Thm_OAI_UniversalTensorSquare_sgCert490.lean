-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert490
-- name    : OAI.UniversalTensorSquare.sgCert490
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:08:23.344212+00:00
-- url     : https://prove2.me/theorems/bcb5d9fd-1f85-43fd-907a-7ed40ff8a86b
-- title:
--   OAI.UniversalTensorSquare.sgCert490: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert490` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert490 : solveCompact 9 (.full [5,4]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
--       (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [5,4] (Equiv.refl (Fin 9)) sgB490 sgT490) sgFlag490 = 2
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB490` and `OAI.UniversalTensorSquare.sgFlag490` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT490` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree26_18All`, `OAI.UniversalTensorSquare.degreeTree26_41All`, `OAI.UniversalTensorSquare.sg13434`, `OAI.UniversalTensorSquare.sg34472`, `OAI.UniversalTensorSquare.sg34475`, `OAI.UniversalTensorSquare.sg34477`, `OAI.UniversalTensorSquare.sg36150`, `OAI.UniversalTensorSquare.sg36153`, `OAI.UniversalTensorSquare.sg36155`, `OAI.UniversalTensorSquare.sg40714`, `OAI.UniversalTensorSquare.sg40716`, `OAI.UniversalTensorSquare.sg41117`, `OAI.UniversalTensorSquare.sg41119`, `OAI.UniversalTensorSquare.sg41142`, `OAI.UniversalTensorSquare.sg41144`, `OAI.UniversalTensorSquare.sg41271`, `OAI.UniversalTensorSquare.sg41273`, `OAI.UniversalTensorSquare.sg41340`, `OAI.UniversalTensorSquare.sg41342`, `OAI.UniversalTensorSquare.sg41386`, `OAI.UniversalTensorSquare.sg41388`, `OAI.UniversalTensorSquare.sg41440`, `OAI.UniversalTensorSquare.sg41442`, `OAI.UniversalTensorSquare.sg41460`, `OAI.UniversalTensorSquare.sg42126`, `OAI.UniversalTensorSquare.sg42816`, `OAI.UniversalTensorSquare.sg42819`, `OAI.UniversalTensorSquare.sg42891`, `OAI.UniversalTensorSquare.sg42894`, `OAI.UniversalTensorSquare.sg42895`, `OAI.UniversalTensorSquare.sg42958`, `OAI.UniversalTensorSquare.sg42998`, `OAI.UniversalTensorSquare.sg42999`, `OAI.UniversalTensorSquare.sg43007`, `OAI.UniversalTensorSquare.sg43008`, `OAI.UniversalTensorSquare.sg43065`, `OAI.UniversalTensorSquare.sg43068`, `OAI.UniversalTensorSquare.sg43115`, `OAI.UniversalTensorSquare.sg43130`, `OAI.UniversalTensorSquare.sg43141` and `OAI.UniversalTensorSquare.sg490` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean (declaration OAI.UniversalTensorSquare.sgCert490)

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

lemma sgCert490 : solveCompact 9 (.full [5,4]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [5,4] (Equiv.refl (Fin 9)) sgB490 sgT490) sgFlag490 = 2 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
