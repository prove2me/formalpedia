-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert636
-- name    : OAI.UniversalTensorSquare.sgCert636
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:19:51.925022+00:00
-- url     : https://prove2.me/theorems/2cddcbe0-10c9-4488-9e69-a347e50e25cf
-- title:
--   OAI.UniversalTensorSquare.sgCert636: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert636` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert636 : solveCompact 9 (.full [6,3]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
--       (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [6,3] (Equiv.refl (Fin 9)) sgB636 sgT636) sgFlag636 = -6
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB636` and `OAI.UniversalTensorSquare.sgFlag636` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT636` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree26_11All`, `OAI.UniversalTensorSquare.sg16293`, `OAI.UniversalTensorSquare.sg16442`, `OAI.UniversalTensorSquare.sg16446`, `OAI.UniversalTensorSquare.sg16497`, `OAI.UniversalTensorSquare.sg17617`, `OAI.UniversalTensorSquare.sg17645`, `OAI.UniversalTensorSquare.sg31868`, `OAI.UniversalTensorSquare.sg34128`, `OAI.UniversalTensorSquare.sg34384`, `OAI.UniversalTensorSquare.sg34386`, `OAI.UniversalTensorSquare.sg34880`, `OAI.UniversalTensorSquare.sg34892`, `OAI.UniversalTensorSquare.sg34894`, `OAI.UniversalTensorSquare.sg34896`, `OAI.UniversalTensorSquare.sg34898`, `OAI.UniversalTensorSquare.sg35003`, `OAI.UniversalTensorSquare.sg35004`, `OAI.UniversalTensorSquare.sg35005`, `OAI.UniversalTensorSquare.sg35009`, `OAI.UniversalTensorSquare.sg35051`, `OAI.UniversalTensorSquare.sg35052`, `OAI.UniversalTensorSquare.sg35053`, `OAI.UniversalTensorSquare.sg35175`, `OAI.UniversalTensorSquare.sg35342`, `OAI.UniversalTensorSquare.sg36020`, `OAI.UniversalTensorSquare.sg36021`, `OAI.UniversalTensorSquare.sg36457`, `OAI.UniversalTensorSquare.sg37334`, `OAI.UniversalTensorSquare.sg37396`, `OAI.UniversalTensorSquare.sg37437`, `OAI.UniversalTensorSquare.sg37450`, `OAI.UniversalTensorSquare.sg37836`, `OAI.UniversalTensorSquare.sg38438`, `OAI.UniversalTensorSquare.sg38457`, `OAI.UniversalTensorSquare.sg38460`, `OAI.UniversalTensorSquare.sg38462`, `OAI.UniversalTensorSquare.sg38559`, `OAI.UniversalTensorSquare.sg38569`, `OAI.UniversalTensorSquare.sg38572`, `OAI.UniversalTensorSquare.sg38574`, `OAI.UniversalTensorSquare.sg38583`, `OAI.UniversalTensorSquare.sg38682`, `OAI.UniversalTensorSquare.sg39232`, `OAI.UniversalTensorSquare.sg39249`, `OAI.UniversalTensorSquare.sg39252`, `OAI.UniversalTensorSquare.sg39254`, `OAI.UniversalTensorSquare.sg39696`, `OAI.UniversalTensorSquare.sg39711`, `OAI.UniversalTensorSquare.sg41255`, `OAI.UniversalTensorSquare.sg41345`, `OAI.UniversalTensorSquare.sg41378`, `OAI.UniversalTensorSquare.sg41380`, `OAI.UniversalTensorSquare.sg41396`, `OAI.UniversalTensorSquare.sg41704`, `OAI.UniversalTensorSquare.sg41866`, `OAI.UniversalTensorSquare.sg41896`, `OAI.UniversalTensorSquare.sg41965`, `OAI.UniversalTensorSquare.sg42221`, `OAI.UniversalTensorSquare.sg43182`, `OAI.UniversalTensorSquare.sg636`, `OAI.UniversalTensorSquare.sg7882` and `OAI.UniversalTensorSquare.sg8489` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean (declaration OAI.UniversalTensorSquare.sgCert636)

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

lemma sgCert636 : solveCompact 9 (.full [6,3]) (.full [3,3,1,1,1]) (.full [3,3,1,1,1])
    (certificateEdges [3,3,1,1,1] [3,3,1,1,1] [6,3] (Equiv.refl (Fin 9)) sgB636 sgT636) sgFlag636 = -6 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
