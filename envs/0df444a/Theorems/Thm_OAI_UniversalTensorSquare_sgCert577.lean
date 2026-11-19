-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert577
-- name    : OAI.UniversalTensorSquare.sgCert577
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:17:59.737026+00:00
-- url     : https://prove2.me/theorems/635971cd-03e2-4962-810f-7484083f14b1
-- title:
--   OAI.UniversalTensorSquare.sgCert577: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert577` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert577 : solveCompact 9 (.full [7,2]) (.full [3,3,2,1]) (.full [3,3,2,1])
--       (certificateEdges [3,3,2,1] [3,3,2,1] [7,2] (Equiv.refl (Fin 9)) sgB577 sgT577) sgFlag577 = 30
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB577` and `OAI.UniversalTensorSquare.sgFlag577` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT577` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_527All`, `OAI.UniversalTensorSquare.degreeTree62_532All`, `OAI.UniversalTensorSquare.degreeTree62_633All`, `OAI.UniversalTensorSquare.sg16586`, `OAI.UniversalTensorSquare.sg17843`, `OAI.UniversalTensorSquare.sg17921`, `OAI.UniversalTensorSquare.sg17946`, `OAI.UniversalTensorSquare.sg17948`, `OAI.UniversalTensorSquare.sg36404`, `OAI.UniversalTensorSquare.sg37846`, `OAI.UniversalTensorSquare.sg38982`, `OAI.UniversalTensorSquare.sg39054`, `OAI.UniversalTensorSquare.sg39100`, `OAI.UniversalTensorSquare.sg39102`, `OAI.UniversalTensorSquare.sg39264`, `OAI.UniversalTensorSquare.sg39471`, `OAI.UniversalTensorSquare.sg39499`, `OAI.UniversalTensorSquare.sg39559`, `OAI.UniversalTensorSquare.sg39630`, `OAI.UniversalTensorSquare.sg40051`, `OAI.UniversalTensorSquare.sg40122`, `OAI.UniversalTensorSquare.sg40130`, `OAI.UniversalTensorSquare.sg40150`, `OAI.UniversalTensorSquare.sg40169`, `OAI.UniversalTensorSquare.sg40176`, `OAI.UniversalTensorSquare.sg40217`, `OAI.UniversalTensorSquare.sg40218`, `OAI.UniversalTensorSquare.sg40866`, `OAI.UniversalTensorSquare.sg41992`, `OAI.UniversalTensorSquare.sg42007`, `OAI.UniversalTensorSquare.sg42299`, `OAI.UniversalTensorSquare.sg42446`, `OAI.UniversalTensorSquare.sg42485`, `OAI.UniversalTensorSquare.sg42572`, `OAI.UniversalTensorSquare.sg42653`, `OAI.UniversalTensorSquare.sg42665`, `OAI.UniversalTensorSquare.sg42692`, `OAI.UniversalTensorSquare.sg42711`, `OAI.UniversalTensorSquare.sg42734`, `OAI.UniversalTensorSquare.sg42749`, `OAI.UniversalTensorSquare.sg42761`, `OAI.UniversalTensorSquare.sg43128`, `OAI.UniversalTensorSquare.sg43134`, `OAI.UniversalTensorSquare.sg43217`, `OAI.UniversalTensorSquare.sg43220`, `OAI.UniversalTensorSquare.sg43224` and `OAI.UniversalTensorSquare.sg577` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean (declaration OAI.UniversalTensorSquare.sgCert577)

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

lemma sgCert577 : solveCompact 9 (.full [7,2]) (.full [3,3,2,1]) (.full [3,3,2,1])
    (certificateEdges [3,3,2,1] [3,3,2,1] [7,2] (Equiv.refl (Fin 9)) sgB577 sgT577) sgFlag577 = 30 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
