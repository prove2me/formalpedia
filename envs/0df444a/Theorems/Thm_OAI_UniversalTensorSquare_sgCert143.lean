-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert143
-- name    : OAI.UniversalTensorSquare.sgCert143
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T00:16:53.719523+00:00
-- url     : https://prove2.me/theorems/baacbd6d-77d2-45fe-a1dd-d11bf730dd90
-- title:
--   OAI.UniversalTensorSquare.sgCert143: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert143` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert143 : solveCompact 7 (.full [5,2]) (.full [3,2,1,1]) (.full [3,2,1,1])
--       (certificateEdges [3,2,1,1] [3,2,1,1] [5,2] (Equiv.refl (Fin 7)) sgB143 sgT143) sgFlag143 = 6
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB143`, `OAI.UniversalTensorSquare.sgFlag143` and `OAI.UniversalTensorSquare.sgT143` (definitions bundle `OAIQ259US002` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_238All`, `OAI.UniversalTensorSquare.degreeTree43_342All`, `OAI.UniversalTensorSquare.degreeTree43_43All`, `OAI.UniversalTensorSquare.degreeTree43_501All`, `OAI.UniversalTensorSquare.degreeTree62_147All`, `OAI.UniversalTensorSquare.degreeTree62_178All`, `OAI.UniversalTensorSquare.degreeTree62_641All`, `OAI.UniversalTensorSquare.degreeTree62_654All`, `OAI.UniversalTensorSquare.degreeTree62_672All`, `OAI.UniversalTensorSquare.degreeTree62_736All`, `OAI.UniversalTensorSquare.degreeTree62_913All`, `OAI.UniversalTensorSquare.degreeTree62_947All`, `OAI.UniversalTensorSquare.sg143`, `OAI.UniversalTensorSquare.sg17601`, `OAI.UniversalTensorSquare.sg21921`, `OAI.UniversalTensorSquare.sg21927`, `OAI.UniversalTensorSquare.sg21972`, `OAI.UniversalTensorSquare.sg21983`, `OAI.UniversalTensorSquare.sg23503`, `OAI.UniversalTensorSquare.sg23521`, `OAI.UniversalTensorSquare.sg23544`, `OAI.UniversalTensorSquare.sg26970`, `OAI.UniversalTensorSquare.sg26981`, `OAI.UniversalTensorSquare.sg27080`, `OAI.UniversalTensorSquare.sg27082`, `OAI.UniversalTensorSquare.sg27101`, `OAI.UniversalTensorSquare.sg30463`, `OAI.UniversalTensorSquare.sg30700`, `OAI.UniversalTensorSquare.sg30988`, `OAI.UniversalTensorSquare.sg31113`, `OAI.UniversalTensorSquare.sg31144`, `OAI.UniversalTensorSquare.sg31146`, `OAI.UniversalTensorSquare.sg31148`, `OAI.UniversalTensorSquare.sg31249`, `OAI.UniversalTensorSquare.sg34445`, `OAI.UniversalTensorSquare.sg35490`, `OAI.UniversalTensorSquare.sg38293`, `OAI.UniversalTensorSquare.sg38948`, `OAI.UniversalTensorSquare.sg39227`, `OAI.UniversalTensorSquare.sg39437`, `OAI.UniversalTensorSquare.sg39928`, `OAI.UniversalTensorSquare.sg39932`, `OAI.UniversalTensorSquare.sg39934`, `OAI.UniversalTensorSquare.sg40198`, `OAI.UniversalTensorSquare.sg40200`, `OAI.UniversalTensorSquare.sg41046`, `OAI.UniversalTensorSquare.sg42208`, `OAI.UniversalTensorSquare.sg42524`, `OAI.UniversalTensorSquare.sg43143` and `OAI.UniversalTensorSquare.sg9590` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean (declaration OAI.UniversalTensorSquare.sgCert143)

import Mathlib
import Definitions.Def_OAIQ259US002
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

lemma sgCert143 : solveCompact 7 (.full [5,2]) (.full [3,2,1,1]) (.full [3,2,1,1])
    (certificateEdges [3,2,1,1] [3,2,1,1] [5,2] (Equiv.refl (Fin 7)) sgB143 sgT143) sgFlag143 = 6 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
