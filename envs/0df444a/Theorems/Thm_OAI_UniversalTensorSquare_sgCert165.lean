-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert165
-- name    : OAI.UniversalTensorSquare.sgCert165
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T00:17:05.903779+00:00
-- url     : https://prove2.me/theorems/0c4b15da-9938-497e-b94a-4d892e34fdb1
-- title:
--   OAI.UniversalTensorSquare.sgCert165: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert165` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert165 : solveCompact 7 (.full [6,1]) (.full [3,2,2]) (.full [3,2,2])
--       (certificateEdges [3,2,2] [3,2,2] [6,1] (Equiv.refl (Fin 7)) sgB165 sgT165) sgFlag165 = 15
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB165` and `OAI.UniversalTensorSquare.sgFlag165` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT165` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_577All`, `OAI.UniversalTensorSquare.sg165`, `OAI.UniversalTensorSquare.sg31972`, `OAI.UniversalTensorSquare.sg35595`, `OAI.UniversalTensorSquare.sg35918`, `OAI.UniversalTensorSquare.sg35965`, `OAI.UniversalTensorSquare.sg36063`, `OAI.UniversalTensorSquare.sg36173`, `OAI.UniversalTensorSquare.sg36212`, `OAI.UniversalTensorSquare.sg36598`, `OAI.UniversalTensorSquare.sg36617`, `OAI.UniversalTensorSquare.sg36618`, `OAI.UniversalTensorSquare.sg37074`, `OAI.UniversalTensorSquare.sg37142`, `OAI.UniversalTensorSquare.sg37208`, `OAI.UniversalTensorSquare.sg37308`, `OAI.UniversalTensorSquare.sg37338`, `OAI.UniversalTensorSquare.sg37361`, `OAI.UniversalTensorSquare.sg37402`, `OAI.UniversalTensorSquare.sg37443`, `OAI.UniversalTensorSquare.sg37486`, `OAI.UniversalTensorSquare.sg37493`, `OAI.UniversalTensorSquare.sg37609`, `OAI.UniversalTensorSquare.sg37644`, `OAI.UniversalTensorSquare.sg37674`, `OAI.UniversalTensorSquare.sg38119`, `OAI.UniversalTensorSquare.sg38122`, `OAI.UniversalTensorSquare.sg38132`, `OAI.UniversalTensorSquare.sg38334`, `OAI.UniversalTensorSquare.sg3860`, `OAI.UniversalTensorSquare.sg38856`, `OAI.UniversalTensorSquare.sg38879`, `OAI.UniversalTensorSquare.sg38887`, `OAI.UniversalTensorSquare.sg38898`, `OAI.UniversalTensorSquare.sg39501`, `OAI.UniversalTensorSquare.sg39748`, `OAI.UniversalTensorSquare.sg39856`, `OAI.UniversalTensorSquare.sg40358`, `OAI.UniversalTensorSquare.sg40366`, `OAI.UniversalTensorSquare.sg40509`, `OAI.UniversalTensorSquare.sg40521`, `OAI.UniversalTensorSquare.sg41233`, `OAI.UniversalTensorSquare.sg41235`, `OAI.UniversalTensorSquare.sg42285`, `OAI.UniversalTensorSquare.sg42408`, `OAI.UniversalTensorSquare.sg42628` and `OAI.UniversalTensorSquare.sg42846` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean (declaration OAI.UniversalTensorSquare.sgCert165)

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

lemma sgCert165 : solveCompact 7 (.full [6,1]) (.full [3,2,2]) (.full [3,2,2])
    (certificateEdges [3,2,2] [3,2,2] [6,1] (Equiv.refl (Fin 7)) sgB165 sgT165) sgFlag165 = 15 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
