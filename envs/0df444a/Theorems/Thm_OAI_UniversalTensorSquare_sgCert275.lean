-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert275
-- name    : OAI.UniversalTensorSquare.sgCert275
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-18T00:17:16.875211+00:00
-- url     : https://prove2.me/theorems/7cd82c18-9048-43a0-8edb-f0045de6d11c
-- title:
--   OAI.UniversalTensorSquare.sgCert275: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert275` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert275 : solveCompact 8 (.full [4,2,2]) (.full [3,2,1,1,1]) (.full [3,2,1,1,1])
--       (certificateEdges [3,2,1,1,1] [3,2,1,1,1] [4,2,2] (Equiv.refl (Fin 8)) sgB275 sgT275) sgFlag275 = -1
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB275` and `OAI.UniversalTensorSquare.sgFlag275` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT275` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_589All`, `OAI.UniversalTensorSquare.degreeTree43_593All`, `OAI.UniversalTensorSquare.sg27098`, `OAI.UniversalTensorSquare.sg275`, `OAI.UniversalTensorSquare.sg30820`, `OAI.UniversalTensorSquare.sg38940`, `OAI.UniversalTensorSquare.sg38944`, `OAI.UniversalTensorSquare.sg38946`, `OAI.UniversalTensorSquare.sg41718`, `OAI.UniversalTensorSquare.sg41720`, `OAI.UniversalTensorSquare.sg41817`, `OAI.UniversalTensorSquare.sg41819`, `OAI.UniversalTensorSquare.sg42854`, `OAI.UniversalTensorSquare.sg43024` and `OAI.UniversalTensorSquare.sg43208` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean (declaration OAI.UniversalTensorSquare.sgCert275)

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

lemma sgCert275 : solveCompact 8 (.full [4,2,2]) (.full [3,2,1,1,1]) (.full [3,2,1,1,1])
    (certificateEdges [3,2,1,1,1] [3,2,1,1,1] [4,2,2] (Equiv.refl (Fin 8)) sgB275 sgT275) sgFlag275 = -1 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
