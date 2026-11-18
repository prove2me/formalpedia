-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert314
-- name    : OAI.UniversalTensorSquare.sgCert314
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-18T00:22:33.687249+00:00
-- url     : https://prove2.me/theorems/61ca189c-8b7f-429a-965d-eb3f7926db4c
-- title:
--   OAI.UniversalTensorSquare.sgCert314: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert314` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert314 : solveCompact 8 (.full [5,3]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
--       (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [5,3] (Equiv.refl (Fin 8)) sgB314 sgT314) sgFlag314 = 20
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB314` and `OAI.UniversalTensorSquare.sgFlag314` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT314` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_101All`, `OAI.UniversalTensorSquare.sg24276`, `OAI.UniversalTensorSquare.sg26896`, `OAI.UniversalTensorSquare.sg314`, `OAI.UniversalTensorSquare.sg34741`, `OAI.UniversalTensorSquare.sg34742`, `OAI.UniversalTensorSquare.sg34743`, `OAI.UniversalTensorSquare.sg34754`, `OAI.UniversalTensorSquare.sg34758`, `OAI.UniversalTensorSquare.sg34805`, `OAI.UniversalTensorSquare.sg34806`, `OAI.UniversalTensorSquare.sg34906`, `OAI.UniversalTensorSquare.sg35069`, `OAI.UniversalTensorSquare.sg36808`, `OAI.UniversalTensorSquare.sg37268`, `OAI.UniversalTensorSquare.sg39731`, `OAI.UniversalTensorSquare.sg41069`, `OAI.UniversalTensorSquare.sg41072`, `OAI.UniversalTensorSquare.sg41756`, `OAI.UniversalTensorSquare.sg41960`, `OAI.UniversalTensorSquare.sg42021`, `OAI.UniversalTensorSquare.sg42030`, `OAI.UniversalTensorSquare.sg8884`, `OAI.UniversalTensorSquare.sg9067` and `OAI.UniversalTensorSquare.sg9253` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean (declaration OAI.UniversalTensorSquare.sgCert314)

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

lemma sgCert314 : solveCompact 8 (.full [5,3]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [5,3] (Equiv.refl (Fin 8)) sgB314 sgT314) sgFlag314 = 20 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
