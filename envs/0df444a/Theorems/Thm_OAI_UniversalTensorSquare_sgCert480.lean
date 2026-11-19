-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert480
-- name    : OAI.UniversalTensorSquare.sgCert480
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:08:15.453303+00:00
-- url     : https://prove2.me/theorems/83d520e8-d258-4b72-a190-3b774b77cdd1
-- title:
--   OAI.UniversalTensorSquare.sgCert480: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert480` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert480 : solveCompact 9 (.full [6,3]) (.full [3,2,2,2]) (.full [3,2,2,2])
--       (certificateEdges [3,2,2,2] [3,2,2,2] [6,3] (Equiv.refl (Fin 9)) sgB480 sgT480) sgFlag480 = 45
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB480` and `OAI.UniversalTensorSquare.sgFlag480` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT480` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg13163`, `OAI.UniversalTensorSquare.sg34129`, `OAI.UniversalTensorSquare.sg37307`, `OAI.UniversalTensorSquare.sg37308`, `OAI.UniversalTensorSquare.sg37492`, `OAI.UniversalTensorSquare.sg37493`, `OAI.UniversalTensorSquare.sg39748`, `OAI.UniversalTensorSquare.sg39856`, `OAI.UniversalTensorSquare.sg41317`, `OAI.UniversalTensorSquare.sg41379` and `OAI.UniversalTensorSquare.sg480` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean (declaration OAI.UniversalTensorSquare.sgCert480)

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

lemma sgCert480 : solveCompact 9 (.full [6,3]) (.full [3,2,2,2]) (.full [3,2,2,2])
    (certificateEdges [3,2,2,2] [3,2,2,2] [6,3] (Equiv.refl (Fin 9)) sgB480 sgT480) sgFlag480 = 45 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
