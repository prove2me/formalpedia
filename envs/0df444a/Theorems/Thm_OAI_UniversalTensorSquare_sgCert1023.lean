-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert1023
-- name    : OAI.UniversalTensorSquare.sgCert1023
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T00:13:47.278139+00:00
-- url     : https://prove2.me/theorems/5f2daa92-dae7-4668-b9c6-839da26363af
-- title:
--   OAI.UniversalTensorSquare.sgCert1023: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert1023` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert1023 : solveCompact 10 (.full [2,2,2,2,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
--       (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [2,2,2,2,2] (Equiv.refl (Fin 10)) sgB1023 sgT1023) sgFlag1023 = -6
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB1023` and `OAI.UniversalTensorSquare.sgFlag1023` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT1023` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_527All`, `OAI.UniversalTensorSquare.sg1023`, `OAI.UniversalTensorSquare.sg20884`, `OAI.UniversalTensorSquare.sg32026`, `OAI.UniversalTensorSquare.sg32268`, `OAI.UniversalTensorSquare.sg32562`, `OAI.UniversalTensorSquare.sg32858`, `OAI.UniversalTensorSquare.sg33051`, `OAI.UniversalTensorSquare.sg34239`, `OAI.UniversalTensorSquare.sg34269`, `OAI.UniversalTensorSquare.sg34382`, `OAI.UniversalTensorSquare.sg34414`, `OAI.UniversalTensorSquare.sg34440`, `OAI.UniversalTensorSquare.sg34554`, `OAI.UniversalTensorSquare.sg34574`, `OAI.UniversalTensorSquare.sg34578`, `OAI.UniversalTensorSquare.sg34603`, `OAI.UniversalTensorSquare.sg34935`, `OAI.UniversalTensorSquare.sg34941`, `OAI.UniversalTensorSquare.sg35050`, `OAI.UniversalTensorSquare.sg35082`, `OAI.UniversalTensorSquare.sg35086`, `OAI.UniversalTensorSquare.sg35104`, `OAI.UniversalTensorSquare.sg35108`, `OAI.UniversalTensorSquare.sg35227`, `OAI.UniversalTensorSquare.sg35231`, `OAI.UniversalTensorSquare.sg35246`, `OAI.UniversalTensorSquare.sg35256`, `OAI.UniversalTensorSquare.sg35338`, `OAI.UniversalTensorSquare.sg35342`, `OAI.UniversalTensorSquare.sg35356`, `OAI.UniversalTensorSquare.sg35366`, `OAI.UniversalTensorSquare.sg35372`, `OAI.UniversalTensorSquare.sg35374`, `OAI.UniversalTensorSquare.sg35429`, `OAI.UniversalTensorSquare.sg35445`, `OAI.UniversalTensorSquare.sg35461`, `OAI.UniversalTensorSquare.sg35470`, `OAI.UniversalTensorSquare.sg35500`, `OAI.UniversalTensorSquare.sg35525`, `OAI.UniversalTensorSquare.sg35581`, `OAI.UniversalTensorSquare.sg35634`, `OAI.UniversalTensorSquare.sg35635`, `OAI.UniversalTensorSquare.sg35644`, `OAI.UniversalTensorSquare.sg35688`, `OAI.UniversalTensorSquare.sg35835`, `OAI.UniversalTensorSquare.sg35836`, `OAI.UniversalTensorSquare.sg36263`, `OAI.UniversalTensorSquare.sg36296`, `OAI.UniversalTensorSquare.sg36297`, `OAI.UniversalTensorSquare.sg36354`, `OAI.UniversalTensorSquare.sg36508`, `OAI.UniversalTensorSquare.sg36514`, `OAI.UniversalTensorSquare.sg36564`, `OAI.UniversalTensorSquare.sg36566`, `OAI.UniversalTensorSquare.sg36668`, `OAI.UniversalTensorSquare.sg36674`, `OAI.UniversalTensorSquare.sg36839`, `OAI.UniversalTensorSquare.sg36960`, `OAI.UniversalTensorSquare.sg37268`, `OAI.UniversalTensorSquare.sg38981` and `OAI.UniversalTensorSquare.sg4939` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean (declaration OAI.UniversalTensorSquare.sgCert1023)

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

lemma sgCert1023 : solveCompact 10 (.full [2,2,2,2,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [2,2,2,2,2] (Equiv.refl (Fin 10)) sgB1023 sgT1023) sgFlag1023 = -6 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
