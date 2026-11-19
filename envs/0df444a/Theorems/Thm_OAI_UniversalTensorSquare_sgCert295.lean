-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert295
-- name    : OAI.UniversalTensorSquare.sgCert295
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T00:19:12.133929+00:00
-- url     : https://prove2.me/theorems/3e09956d-7dfe-437e-9ea2-c8baafe29dc0
-- title:
--   OAI.UniversalTensorSquare.sgCert295: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert295` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert295 : solveCompact 8 (.full [6,2]) (.full [3,3,1,1]) (.full [3,3,1,1])
--       (certificateEdges [3,3,1,1] [3,3,1,1] [6,2] (Equiv.refl (Fin 8)) sgB295 sgT295) sgFlag295 = 10
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB295` and `OAI.UniversalTensorSquare.sgFlag295` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT295` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_88All`, `OAI.UniversalTensorSquare.sg23555`, `OAI.UniversalTensorSquare.sg295`, `OAI.UniversalTensorSquare.sg34610`, `OAI.UniversalTensorSquare.sg38916`, `OAI.UniversalTensorSquare.sg39530`, `OAI.UniversalTensorSquare.sg39984`, `OAI.UniversalTensorSquare.sg40039`, `OAI.UniversalTensorSquare.sg41882`, `OAI.UniversalTensorSquare.sg41915`, `OAI.UniversalTensorSquare.sg41929`, `OAI.UniversalTensorSquare.sg41980`, `OAI.UniversalTensorSquare.sg42039`, `OAI.UniversalTensorSquare.sg42261`, `OAI.UniversalTensorSquare.sg42273`, `OAI.UniversalTensorSquare.sg42317`, `OAI.UniversalTensorSquare.sg42384`, `OAI.UniversalTensorSquare.sg42396`, `OAI.UniversalTensorSquare.sg42584`, `OAI.UniversalTensorSquare.sg42607`, `OAI.UniversalTensorSquare.sg42617`, `OAI.UniversalTensorSquare.sg42682`, `OAI.UniversalTensorSquare.sg42691`, `OAI.UniversalTensorSquare.sg42716`, `OAI.UniversalTensorSquare.sg42746`, `OAI.UniversalTensorSquare.sg42767`, `OAI.UniversalTensorSquare.sg43116`, `OAI.UniversalTensorSquare.sg43122`, `OAI.UniversalTensorSquare.sg43131`, `OAI.UniversalTensorSquare.sg43136` and `OAI.UniversalTensorSquare.sg7928` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean (declaration OAI.UniversalTensorSquare.sgCert295)

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

lemma sgCert295 : solveCompact 8 (.full [6,2]) (.full [3,3,1,1]) (.full [3,3,1,1])
    (certificateEdges [3,3,1,1] [3,3,1,1] [6,2] (Equiv.refl (Fin 8)) sgB295 sgT295) sgFlag295 = 10 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
