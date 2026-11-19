-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert998
-- name    : OAI.UniversalTensorSquare.sgCert998
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:49:42.024698+00:00
-- url     : https://prove2.me/theorems/4e147c5b-c8e5-4200-b17f-25cc19003020
-- title:
--   OAI.UniversalTensorSquare.sgCert998: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert998` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert998 : solveCompact 10 (.full [8,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
--       (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [8,2] (Equiv.refl (Fin 10)) sgB998 sgT998) sgFlag998 = -288
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB998` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgFlag998` and `OAI.UniversalTensorSquare.sgT998` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg17426`, `OAI.UniversalTensorSquare.sg21797`, `OAI.UniversalTensorSquare.sg24059`, `OAI.UniversalTensorSquare.sg24130`, `OAI.UniversalTensorSquare.sg25513`, `OAI.UniversalTensorSquare.sg26298`, `OAI.UniversalTensorSquare.sg29308`, `OAI.UniversalTensorSquare.sg30168`, `OAI.UniversalTensorSquare.sg35703`, `OAI.UniversalTensorSquare.sg35707`, `OAI.UniversalTensorSquare.sg35754`, `OAI.UniversalTensorSquare.sg35755`, `OAI.UniversalTensorSquare.sg35801`, `OAI.UniversalTensorSquare.sg36404`, `OAI.UniversalTensorSquare.sg36406`, `OAI.UniversalTensorSquare.sg36537`, `OAI.UniversalTensorSquare.sg36710`, `OAI.UniversalTensorSquare.sg36713`, `OAI.UniversalTensorSquare.sg36715`, `OAI.UniversalTensorSquare.sg37862`, `OAI.UniversalTensorSquare.sg37933`, `OAI.UniversalTensorSquare.sg38073`, `OAI.UniversalTensorSquare.sg38078`, `OAI.UniversalTensorSquare.sg39394`, `OAI.UniversalTensorSquare.sg39530`, `OAI.UniversalTensorSquare.sg39984`, `OAI.UniversalTensorSquare.sg40039`, `OAI.UniversalTensorSquare.sg40266`, `OAI.UniversalTensorSquare.sg40399`, `OAI.UniversalTensorSquare.sg40872`, `OAI.UniversalTensorSquare.sg40874`, `OAI.UniversalTensorSquare.sg40875`, `OAI.UniversalTensorSquare.sg40963`, `OAI.UniversalTensorSquare.sg40965`, `OAI.UniversalTensorSquare.sg40966`, `OAI.UniversalTensorSquare.sg41555`, `OAI.UniversalTensorSquare.sg41557`, `OAI.UniversalTensorSquare.sg42793`, `OAI.UniversalTensorSquare.sg42857`, `OAI.UniversalTensorSquare.sg42870`, `OAI.UniversalTensorSquare.sg42879`, `OAI.UniversalTensorSquare.sg42894`, `OAI.UniversalTensorSquare.sg43030`, `OAI.UniversalTensorSquare.sg43039`, `OAI.UniversalTensorSquare.sg43044`, `OAI.UniversalTensorSquare.sg43065`, `OAI.UniversalTensorSquare.sg43087`, `OAI.UniversalTensorSquare.sg43092`, `OAI.UniversalTensorSquare.sg4546`, `OAI.UniversalTensorSquare.sg5778`, `OAI.UniversalTensorSquare.sg6182`, `OAI.UniversalTensorSquare.sg6771`, `OAI.UniversalTensorSquare.sg7078`, `OAI.UniversalTensorSquare.sg7081`, `OAI.UniversalTensorSquare.sg7087`, `OAI.UniversalTensorSquare.sg7191`, `OAI.UniversalTensorSquare.sg7194`, `OAI.UniversalTensorSquare.sg7208`, `OAI.UniversalTensorSquare.sg7211`, `OAI.UniversalTensorSquare.sg7225`, `OAI.UniversalTensorSquare.sg7250`, `OAI.UniversalTensorSquare.sg7316`, `OAI.UniversalTensorSquare.sg7377`, `OAI.UniversalTensorSquare.sg7395`, `OAI.UniversalTensorSquare.sg7401`, `OAI.UniversalTensorSquare.sg7528`, `OAI.UniversalTensorSquare.sg7575`, `OAI.UniversalTensorSquare.sg7578`, `OAI.UniversalTensorSquare.sg7580`, `OAI.UniversalTensorSquare.sg7646`, `OAI.UniversalTensorSquare.sg7649`, `OAI.UniversalTensorSquare.sg7679`, `OAI.UniversalTensorSquare.sg7682`, `OAI.UniversalTensorSquare.sg7711`, `OAI.UniversalTensorSquare.sg7753`, `OAI.UniversalTensorSquare.sg8441`, `OAI.UniversalTensorSquare.sg8479`, `OAI.UniversalTensorSquare.sg8532`, `OAI.UniversalTensorSquare.sg9042`, `OAI.UniversalTensorSquare.sg9240`, `OAI.UniversalTensorSquare.sg9245`, `OAI.UniversalTensorSquare.sg9247`, `OAI.UniversalTensorSquare.sg9263`, `OAI.UniversalTensorSquare.sg9269`, `OAI.UniversalTensorSquare.sg9295`, `OAI.UniversalTensorSquare.sg9325`, `OAI.UniversalTensorSquare.sg9730`, `OAI.UniversalTensorSquare.sg9745`, `OAI.UniversalTensorSquare.sg9788`, `OAI.UniversalTensorSquare.sg9818`, `OAI.UniversalTensorSquare.sg9850`, `OAI.UniversalTensorSquare.sg9882`, `OAI.UniversalTensorSquare.sg9898`, `OAI.UniversalTensorSquare.sg9962` and `OAI.UniversalTensorSquare.sg998` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean (declaration OAI.UniversalTensorSquare.sgCert998)

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

lemma sgCert998 : solveCompact 10 (.full [8,2]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [8,2] (Equiv.refl (Fin 10)) sgB998 sgT998) sgFlag998 = -288 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
