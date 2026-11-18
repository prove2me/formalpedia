-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert1063
-- name    : OAI.UniversalTensorSquare.sgCert1063
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-18T00:16:55.502004+00:00
-- url     : https://prove2.me/theorems/1c6b32a5-41b2-4b64-b47e-5a91daab2856
-- title:
--   OAI.UniversalTensorSquare.sgCert1063: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert1063` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert1063 : solveCompact 10 (.full [6,2,2]) (.full [3,3,1,1,1,1]) (.full [3,3,1,1,1,1])
--       (certificateEdges [3,3,1,1,1,1] [3,3,1,1,1,1] [6,2,2] (Equiv.refl (Fin 10)) sgB1063 sgT1063) sgFlag1063 = -16
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB1063` and `OAI.UniversalTensorSquare.sgFlag1063` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT1063` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree22_4All`, `OAI.UniversalTensorSquare.degreeTree26_18All`, `OAI.UniversalTensorSquare.degreeTree26_41All`, `OAI.UniversalTensorSquare.sg16479`, `OAI.UniversalTensorSquare.sg16586`, `OAI.UniversalTensorSquare.sg16594`, `OAI.UniversalTensorSquare.sg16600`, `OAI.UniversalTensorSquare.sg24031`, `OAI.UniversalTensorSquare.sg26224`, `OAI.UniversalTensorSquare.sg37763`, `OAI.UniversalTensorSquare.sg37846`, `OAI.UniversalTensorSquare.sg38313`, `OAI.UniversalTensorSquare.sg38979`, `OAI.UniversalTensorSquare.sg39162`, `OAI.UniversalTensorSquare.sg39363`, `OAI.UniversalTensorSquare.sg39471`, `OAI.UniversalTensorSquare.sg39964`, `OAI.UniversalTensorSquare.sg39965`, `OAI.UniversalTensorSquare.sg40222`, `OAI.UniversalTensorSquare.sg41704`, `OAI.UniversalTensorSquare.sg41751`, `OAI.UniversalTensorSquare.sg42157`, `OAI.UniversalTensorSquare.sg42171`, `OAI.UniversalTensorSquare.sg42221`, `OAI.UniversalTensorSquare.sg42351`, `OAI.UniversalTensorSquare.sg42575`, `OAI.UniversalTensorSquare.sg42643` and `OAI.UniversalTensorSquare.sg7893` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean (declaration OAI.UniversalTensorSquare.sgCert1063)

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

lemma sgCert1063 : solveCompact 10 (.full [6,2,2]) (.full [3,3,1,1,1,1]) (.full [3,3,1,1,1,1])
    (certificateEdges [3,3,1,1,1,1] [3,3,1,1,1,1] [6,2,2] (Equiv.refl (Fin 10)) sgB1063 sgT1063) sgFlag1063 = -16 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
