-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert958
-- name    : OAI.UniversalTensorSquare.sgCert958
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:47:48.811947+00:00
-- url     : https://prove2.me/theorems/922bb6d8-a5c3-43d0-a637-1c0d213eec07
-- title:
--   OAI.UniversalTensorSquare.sgCert958: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert958` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert958 : solveCompact 10 (.full [8,2]) (.full [4,2,2,1,1]) (.full [4,2,2,1,1])
--       (certificateEdges [4,2,2,1,1] [4,2,2,1,1] [8,2] (Equiv.refl (Fin 10)) sgB958 sgT958) sgFlag958 = -112
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB958` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgFlag958` and `OAI.UniversalTensorSquare.sgT958` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg12045`, `OAI.UniversalTensorSquare.sg22328`, `OAI.UniversalTensorSquare.sg23524`, `OAI.UniversalTensorSquare.sg27001`, `OAI.UniversalTensorSquare.sg27012`, `OAI.UniversalTensorSquare.sg27071`, `OAI.UniversalTensorSquare.sg31137`, `OAI.UniversalTensorSquare.sg37775`, `OAI.UniversalTensorSquare.sg37781`, `OAI.UniversalTensorSquare.sg38927`, `OAI.UniversalTensorSquare.sg38933`, `OAI.UniversalTensorSquare.sg40791`, `OAI.UniversalTensorSquare.sg40794`, `OAI.UniversalTensorSquare.sg40795`, `OAI.UniversalTensorSquare.sg6771`, `OAI.UniversalTensorSquare.sg6773`, `OAI.UniversalTensorSquare.sg6775`, `OAI.UniversalTensorSquare.sg6777` and `OAI.UniversalTensorSquare.sg958` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean (declaration OAI.UniversalTensorSquare.sgCert958)

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

lemma sgCert958 : solveCompact 10 (.full [8,2]) (.full [4,2,2,1,1]) (.full [4,2,2,1,1])
    (certificateEdges [4,2,2,1,1] [4,2,2,1,1] [8,2] (Equiv.refl (Fin 10)) sgB958 sgT958) sgFlag958 = -112 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
