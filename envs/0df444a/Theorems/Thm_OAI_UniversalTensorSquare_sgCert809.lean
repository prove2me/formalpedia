-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert809
-- name    : OAI.UniversalTensorSquare.sgCert809
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:23:24.583195+00:00
-- url     : https://prove2.me/theorems/196e22fa-5283-4aff-85dd-7af2bfa4f4e7
-- title:
--   OAI.UniversalTensorSquare.sgCert809: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert809` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert809 : solveCompact 10 (.full [5,5]) (.full [4,2,1,1,1,1]) (.full [4,2,1,1,1,1])
--       (certificateEdges [4,2,1,1,1,1] [4,2,1,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB809 sgT809) sgFlag809 = -40
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB809` and `OAI.UniversalTensorSquare.sgFlag809` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT809` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg21929`, `OAI.UniversalTensorSquare.sg24550`, `OAI.UniversalTensorSquare.sg25221`, `OAI.UniversalTensorSquare.sg25327`, `OAI.UniversalTensorSquare.sg25564`, `OAI.UniversalTensorSquare.sg27305`, `OAI.UniversalTensorSquare.sg31340`, `OAI.UniversalTensorSquare.sg36315`, `OAI.UniversalTensorSquare.sg36316`, `OAI.UniversalTensorSquare.sg36319`, `OAI.UniversalTensorSquare.sg36321`, `OAI.UniversalTensorSquare.sg37285`, `OAI.UniversalTensorSquare.sg37288`, `OAI.UniversalTensorSquare.sg37289`, `OAI.UniversalTensorSquare.sg38568`, `OAI.UniversalTensorSquare.sg38571`, `OAI.UniversalTensorSquare.sg42017`, `OAI.UniversalTensorSquare.sg42679`, `OAI.UniversalTensorSquare.sg42680`, `OAI.UniversalTensorSquare.sg4304`, `OAI.UniversalTensorSquare.sg6410` and `OAI.UniversalTensorSquare.sg809` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean (declaration OAI.UniversalTensorSquare.sgCert809)

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

lemma sgCert809 : solveCompact 10 (.full [5,5]) (.full [4,2,1,1,1,1]) (.full [4,2,1,1,1,1])
    (certificateEdges [4,2,1,1,1,1] [4,2,1,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB809 sgT809) sgFlag809 = -40 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
