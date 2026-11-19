-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert548
-- name    : OAI.UniversalTensorSquare.sgCert548
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:17:45.360772+00:00
-- url     : https://prove2.me/theorems/e7e7530d-d1ab-4140-a56b-8899a5b57503
-- title:
--   OAI.UniversalTensorSquare.sgCert548: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert548` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert548 : solveCompact 9 (.full [8,1]) (.full [4,2,2,1]) (.full [4,2,2,1])
--       (certificateEdges [4,2,2,1] [4,2,2,1] [8,1] (Equiv.refl (Fin 9)) sgB548 sgT548) sgFlag548 = 56
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB548` and `OAI.UniversalTensorSquare.sgFlag548` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT548` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_56All`, `OAI.UniversalTensorSquare.degreeTree43_60All`, `OAI.UniversalTensorSquare.degreeTree62_496All`, `OAI.UniversalTensorSquare.degreeTree62_796All`, `OAI.UniversalTensorSquare.sg10935`, `OAI.UniversalTensorSquare.sg12110`, `OAI.UniversalTensorSquare.sg12214`, `OAI.UniversalTensorSquare.sg27659`, `OAI.UniversalTensorSquare.sg3422`, `OAI.UniversalTensorSquare.sg35484`, `OAI.UniversalTensorSquare.sg35486`, `OAI.UniversalTensorSquare.sg35540`, `OAI.UniversalTensorSquare.sg35542`, `OAI.UniversalTensorSquare.sg37120`, `OAI.UniversalTensorSquare.sg37123`, `OAI.UniversalTensorSquare.sg37125`, `OAI.UniversalTensorSquare.sg37175`, `OAI.UniversalTensorSquare.sg37178`, `OAI.UniversalTensorSquare.sg37180`, `OAI.UniversalTensorSquare.sg37331`, `OAI.UniversalTensorSquare.sg40321`, `OAI.UniversalTensorSquare.sg40554`, `OAI.UniversalTensorSquare.sg40556`, `OAI.UniversalTensorSquare.sg40557`, `OAI.UniversalTensorSquare.sg40588`, `OAI.UniversalTensorSquare.sg40590`, `OAI.UniversalTensorSquare.sg40591`, `OAI.UniversalTensorSquare.sg40664`, `OAI.UniversalTensorSquare.sg40666`, `OAI.UniversalTensorSquare.sg40667`, `OAI.UniversalTensorSquare.sg40676`, `OAI.UniversalTensorSquare.sg40678`, `OAI.UniversalTensorSquare.sg40679`, `OAI.UniversalTensorSquare.sg41209`, `OAI.UniversalTensorSquare.sg41211`, `OAI.UniversalTensorSquare.sg41212`, `OAI.UniversalTensorSquare.sg41251`, `OAI.UniversalTensorSquare.sg41253`, `OAI.UniversalTensorSquare.sg41254`, `OAI.UniversalTensorSquare.sg41326`, `OAI.UniversalTensorSquare.sg41330`, `OAI.UniversalTensorSquare.sg41331`, `OAI.UniversalTensorSquare.sg4926`, `OAI.UniversalTensorSquare.sg548`, `OAI.UniversalTensorSquare.sg7974` and `OAI.UniversalTensorSquare.sg7980` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean (declaration OAI.UniversalTensorSquare.sgCert548)

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

lemma sgCert548 : solveCompact 9 (.full [8,1]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [8,1] (Equiv.refl (Fin 9)) sgB548 sgT548) sgFlag548 = 56 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
