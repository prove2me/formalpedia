-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert551
-- name    : OAI.UniversalTensorSquare.sgCert551
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:17:37.98364+00:00
-- url     : https://prove2.me/theorems/6ce6ba52-5287-4bc2-a202-1f8032aeb846
-- title:
--   OAI.UniversalTensorSquare.sgCert551: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert551` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert551 : solveCompact 9 (.full [5,4]) (.full [4,2,2,1]) (.full [4,2,2,1])
--       (certificateEdges [4,2,2,1] [4,2,2,1] [5,4] (Equiv.refl (Fin 9)) sgB551 sgT551) sgFlag551 = -3
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB551` and `OAI.UniversalTensorSquare.sgFlag551` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT551` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg29902`, `OAI.UniversalTensorSquare.sg34349`, `OAI.UniversalTensorSquare.sg34350`, `OAI.UniversalTensorSquare.sg34392`, `OAI.UniversalTensorSquare.sg34394`, `OAI.UniversalTensorSquare.sg34496`, `OAI.UniversalTensorSquare.sg35034`, `OAI.UniversalTensorSquare.sg35038`, `OAI.UniversalTensorSquare.sg35040`, `OAI.UniversalTensorSquare.sg35182`, `OAI.UniversalTensorSquare.sg35195`, `OAI.UniversalTensorSquare.sg35217`, `OAI.UniversalTensorSquare.sg35335`, `OAI.UniversalTensorSquare.sg35346`, `OAI.UniversalTensorSquare.sg35349`, `OAI.UniversalTensorSquare.sg35350`, `OAI.UniversalTensorSquare.sg35351`, `OAI.UniversalTensorSquare.sg35415`, `OAI.UniversalTensorSquare.sg35435`, `OAI.UniversalTensorSquare.sg35438`, `OAI.UniversalTensorSquare.sg551` and `OAI.UniversalTensorSquare.sg8467` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean (declaration OAI.UniversalTensorSquare.sgCert551)

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

lemma sgCert551 : solveCompact 9 (.full [5,4]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [5,4] (Equiv.refl (Fin 9)) sgB551 sgT551) sgFlag551 = -3 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
