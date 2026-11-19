-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert833
-- name    : OAI.UniversalTensorSquare.sgCert833
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:31:26.640416+00:00
-- url     : https://prove2.me/theorems/c49995e0-a31f-4100-aa74-e2bec30074b7
-- title:
--   OAI.UniversalTensorSquare.sgCert833: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert833` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert833 : solveCompact 10 (.full [6,4]) (.full [4,2,2,2]) (.full [4,2,2,2])
--       (certificateEdges [4,2,2,2] [4,2,2,2] [6,4] (Equiv.refl (Fin 10)) sgB833 sgT833) sgFlag833 = 6
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB833` and `OAI.UniversalTensorSquare.sgFlag833` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT833` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg29897`, `OAI.UniversalTensorSquare.sg37608`, `OAI.UniversalTensorSquare.sg37609`, `OAI.UniversalTensorSquare.sg38312`, `OAI.UniversalTensorSquare.sg38714`, `OAI.UniversalTensorSquare.sg38856`, `OAI.UniversalTensorSquare.sg39501`, `OAI.UniversalTensorSquare.sg42377`, `OAI.UniversalTensorSquare.sg42419`, `OAI.UniversalTensorSquare.sg42463`, `OAI.UniversalTensorSquare.sg4328` and `OAI.UniversalTensorSquare.sg8012` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean (declaration OAI.UniversalTensorSquare.sgCert833)

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

lemma sgCert833 : solveCompact 10 (.full [6,4]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [6,4] (Equiv.refl (Fin 10)) sgB833 sgT833) sgFlag833 = 6 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
