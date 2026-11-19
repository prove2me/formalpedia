-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert71
-- name    : OAI.UniversalTensorSquare.sgCert71
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:22:54.950701+00:00
-- url     : https://prove2.me/theorems/880c2293-9b2d-4b62-a820-46c99268feef
-- title:
--   OAI.UniversalTensorSquare.sgCert71: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert71` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert71 : solveCompact 6 (.full [2,2,2]) (.full [3,1,1,1]) (.full [3,1,1,1])
--       (certificateEdges [3,1,1,1] [3,1,1,1] [2,2,2] (Equiv.refl (Fin 6)) sgB71 sgT71) sgFlag71 = 2
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB71` and `OAI.UniversalTensorSquare.sgFlag71` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT71` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree26_41All`, `OAI.UniversalTensorSquare.degreeTreeAll41`, `OAI.UniversalTensorSquare.sg21257`, `OAI.UniversalTensorSquare.sg21259`, `OAI.UniversalTensorSquare.sg21261`, `OAI.UniversalTensorSquare.sg21263`, `OAI.UniversalTensorSquare.sg23242`, `OAI.UniversalTensorSquare.sg23576`, `OAI.UniversalTensorSquare.sg26974`, `OAI.UniversalTensorSquare.sg26976`, `OAI.UniversalTensorSquare.sg26978`, `OAI.UniversalTensorSquare.sg26998`, `OAI.UniversalTensorSquare.sg27652`, `OAI.UniversalTensorSquare.sg27659`, `OAI.UniversalTensorSquare.sg28156`, `OAI.UniversalTensorSquare.sg28158`, `OAI.UniversalTensorSquare.sg29148`, `OAI.UniversalTensorSquare.sg30704`, `OAI.UniversalTensorSquare.sg30706`, `OAI.UniversalTensorSquare.sg30708`, `OAI.UniversalTensorSquare.sg31160`, `OAI.UniversalTensorSquare.sg31247`, `OAI.UniversalTensorSquare.sg31916`, `OAI.UniversalTensorSquare.sg31925`, `OAI.UniversalTensorSquare.sg35728`, `OAI.UniversalTensorSquare.sg35783`, `OAI.UniversalTensorSquare.sg35799`, `OAI.UniversalTensorSquare.sg35802`, `OAI.UniversalTensorSquare.sg35914`, `OAI.UniversalTensorSquare.sg35930`, `OAI.UniversalTensorSquare.sg35946`, `OAI.UniversalTensorSquare.sg35949`, `OAI.UniversalTensorSquare.sg35999`, `OAI.UniversalTensorSquare.sg36056`, `OAI.UniversalTensorSquare.sg36136`, `OAI.UniversalTensorSquare.sg36139`, `OAI.UniversalTensorSquare.sg36157`, `OAI.UniversalTensorSquare.sg36207`, `OAI.UniversalTensorSquare.sg36246`, `OAI.UniversalTensorSquare.sg36456`, `OAI.UniversalTensorSquare.sg36486`, `OAI.UniversalTensorSquare.sg36508`, `OAI.UniversalTensorSquare.sg36564`, `OAI.UniversalTensorSquare.sg36630`, `OAI.UniversalTensorSquare.sg36646`, `OAI.UniversalTensorSquare.sg36668`, `OAI.UniversalTensorSquare.sg36720`, `OAI.UniversalTensorSquare.sg36738`, `OAI.UniversalTensorSquare.sg36768`, `OAI.UniversalTensorSquare.sg36786`, `OAI.UniversalTensorSquare.sg36824`, `OAI.UniversalTensorSquare.sg36880`, `OAI.UniversalTensorSquare.sg36893`, `OAI.UniversalTensorSquare.sg36960`, `OAI.UniversalTensorSquare.sg37086`, `OAI.UniversalTensorSquare.sg37106`, `OAI.UniversalTensorSquare.sg37136`, `OAI.UniversalTensorSquare.sg37191`, `OAI.UniversalTensorSquare.sg37203`, `OAI.UniversalTensorSquare.sg37222`, `OAI.UniversalTensorSquare.sg37240`, `OAI.UniversalTensorSquare.sg37268`, `OAI.UniversalTensorSquare.sg37347`, `OAI.UniversalTensorSquare.sg41521`, `OAI.UniversalTensorSquare.sg42122`, `OAI.UniversalTensorSquare.sg43222`, `OAI.UniversalTensorSquare.sg71` and `OAI.UniversalTensorSquare.sg7413` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean (declaration OAI.UniversalTensorSquare.sgCert71)

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

lemma sgCert71 : solveCompact 6 (.full [2,2,2]) (.full [3,1,1,1]) (.full [3,1,1,1])
    (certificateEdges [3,1,1,1] [3,1,1,1] [2,2,2] (Equiv.refl (Fin 6)) sgB71 sgT71) sgFlag71 = 2 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
