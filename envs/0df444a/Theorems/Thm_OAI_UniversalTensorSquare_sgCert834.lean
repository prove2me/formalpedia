-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert834
-- name    : OAI.UniversalTensorSquare.sgCert834
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:31:35.986748+00:00
-- url     : https://prove2.me/theorems/c8d1f36d-f90a-4865-94ba-56079725ee01
-- title:
--   OAI.UniversalTensorSquare.sgCert834: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert834` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert834 : solveCompact 10 (.full [5,5]) (.full [4,2,2,2]) (.full [4,2,2,2])
--       (certificateEdges [4,2,2,2] [4,2,2,2] [5,5] (Equiv.refl (Fin 10)) sgB834 sgT834) sgFlag834 = 32
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB834` and `OAI.UniversalTensorSquare.sgFlag834` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT834` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg34904`, `OAI.UniversalTensorSquare.sg37643`, `OAI.UniversalTensorSquare.sg37644`, `OAI.UniversalTensorSquare.sg37673`, `OAI.UniversalTensorSquare.sg37674`, `OAI.UniversalTensorSquare.sg38879`, `OAI.UniversalTensorSquare.sg38898`, `OAI.UniversalTensorSquare.sg42474`, `OAI.UniversalTensorSquare.sg4329`, `OAI.UniversalTensorSquare.sg6004`, `OAI.UniversalTensorSquare.sg8013` and `OAI.UniversalTensorSquare.sg834` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean (declaration OAI.UniversalTensorSquare.sgCert834)

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

lemma sgCert834 : solveCompact 10 (.full [5,5]) (.full [4,2,2,2]) (.full [4,2,2,2])
    (certificateEdges [4,2,2,2] [4,2,2,2] [5,5] (Equiv.refl (Fin 10)) sgB834 sgT834) sgFlag834 = 32 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
