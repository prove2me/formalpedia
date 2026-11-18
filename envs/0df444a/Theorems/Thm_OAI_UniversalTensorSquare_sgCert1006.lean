-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert1006
-- name    : OAI.UniversalTensorSquare.sgCert1006
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-18T00:13:33.443842+00:00
-- url     : https://prove2.me/theorems/2c2fef18-8835-4712-a5f1-96f2e3948074
-- title:
--   OAI.UniversalTensorSquare.sgCert1006: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert1006` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert1006 : solveCompact 10 (.full [6,2,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
--       (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [6,2,2] (Equiv.refl (Fin 10)) sgB1006 sgT1006) sgFlag1006 = -12
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB1006` and `OAI.UniversalTensorSquare.sgFlag1006` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT1006` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg1006`, `OAI.UniversalTensorSquare.sg23625`, `OAI.UniversalTensorSquare.sg37968`, `OAI.UniversalTensorSquare.sg40198`, `OAI.UniversalTensorSquare.sg40200`, `OAI.UniversalTensorSquare.sg43213`, `OAI.UniversalTensorSquare.sg4492`, `OAI.UniversalTensorSquare.sg6947`, `OAI.UniversalTensorSquare.sg7085`, `OAI.UniversalTensorSquare.sg7252`, `OAI.UniversalTensorSquare.sg7374`, `OAI.UniversalTensorSquare.sg7583`, `OAI.UniversalTensorSquare.sg7648`, `OAI.UniversalTensorSquare.sg7651`, `OAI.UniversalTensorSquare.sg7715`, `OAI.UniversalTensorSquare.sg9384` and `OAI.UniversalTensorSquare.sg9634` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean (declaration OAI.UniversalTensorSquare.sgCert1006)

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

lemma sgCert1006 : solveCompact 10 (.full [6,2,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [6,2,2] (Equiv.refl (Fin 10)) sgB1006 sgT1006) sgFlag1006 = -12 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
