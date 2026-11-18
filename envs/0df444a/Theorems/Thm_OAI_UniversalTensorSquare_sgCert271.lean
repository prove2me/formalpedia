-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert271
-- name    : OAI.UniversalTensorSquare.sgCert271
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-18T00:17:02.892249+00:00
-- url     : https://prove2.me/theorems/7052c087-47a6-43e0-a41f-6092ed2ee327
-- title:
--   OAI.UniversalTensorSquare.sgCert271: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert271` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert271 : solveCompact 8 (.full [4,4]) (.full [3,2,1,1,1]) (.full [3,2,1,1,1])
--       (certificateEdges [3,2,1,1,1] [3,2,1,1,1] [4,4] (Equiv.refl (Fin 8)) sgB271 sgT271) sgFlag271 = -4
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB271` and `OAI.UniversalTensorSquare.sgFlag271` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT271` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_277All`, `OAI.UniversalTensorSquare.sg24530`, `OAI.UniversalTensorSquare.sg271`, `OAI.UniversalTensorSquare.sg30958`, `OAI.UniversalTensorSquare.sg32562`, `OAI.UniversalTensorSquare.sg35274`, `OAI.UniversalTensorSquare.sg35404`, `OAI.UniversalTensorSquare.sg37532`, `OAI.UniversalTensorSquare.sg37621`, `OAI.UniversalTensorSquare.sg37624`, `OAI.UniversalTensorSquare.sg42509`, `OAI.UniversalTensorSquare.sg42814`, `OAI.UniversalTensorSquare.sg43061`, `OAI.UniversalTensorSquare.sg43235`, `OAI.UniversalTensorSquare.sg43238`, `OAI.UniversalTensorSquare.sg43246`, `OAI.UniversalTensorSquare.sg9287`, `OAI.UniversalTensorSquare.sg9290` and `OAI.UniversalTensorSquare.sg9291` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean (declaration OAI.UniversalTensorSquare.sgCert271)

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

lemma sgCert271 : solveCompact 8 (.full [4,4]) (.full [3,2,1,1,1]) (.full [3,2,1,1,1])
    (certificateEdges [3,2,1,1,1] [3,2,1,1,1] [4,4] (Equiv.refl (Fin 8)) sgB271 sgT271) sgFlag271 = -4 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
