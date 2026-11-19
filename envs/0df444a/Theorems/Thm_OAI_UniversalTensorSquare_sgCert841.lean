-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert841
-- name    : OAI.UniversalTensorSquare.sgCert841
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:31:30.6209+00:00
-- url     : https://prove2.me/theorems/a060112e-6b01-4ece-9806-63689c75f90c
-- title:
--   OAI.UniversalTensorSquare.sgCert841: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert841` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert841 : solveCompact 10 (.full [5,5]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
--       (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB841 sgT841) sgFlag841 = -2
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB841` and `OAI.UniversalTensorSquare.sgFlag841` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT841` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg19169`, `OAI.UniversalTensorSquare.sg20474`, `OAI.UniversalTensorSquare.sg34158`, `OAI.UniversalTensorSquare.sg34308`, `OAI.UniversalTensorSquare.sg34312`, `OAI.UniversalTensorSquare.sg34315`, `OAI.UniversalTensorSquare.sg34317`, `OAI.UniversalTensorSquare.sg34721`, `OAI.UniversalTensorSquare.sg34731`, `OAI.UniversalTensorSquare.sg34734`, `OAI.UniversalTensorSquare.sg34736`, `OAI.UniversalTensorSquare.sg34851`, `OAI.UniversalTensorSquare.sg34855`, `OAI.UniversalTensorSquare.sg34858`, `OAI.UniversalTensorSquare.sg34860`, `OAI.UniversalTensorSquare.sg34976`, `OAI.UniversalTensorSquare.sg34980`, `OAI.UniversalTensorSquare.sg34983`, `OAI.UniversalTensorSquare.sg34985`, `OAI.UniversalTensorSquare.sg36317`, `OAI.UniversalTensorSquare.sg37029`, `OAI.UniversalTensorSquare.sg37032`, `OAI.UniversalTensorSquare.sg37050`, `OAI.UniversalTensorSquare.sg37051`, `OAI.UniversalTensorSquare.sg37203`, `OAI.UniversalTensorSquare.sg37467`, `OAI.UniversalTensorSquare.sg37471`, `OAI.UniversalTensorSquare.sg37474`, `OAI.UniversalTensorSquare.sg37476`, `OAI.UniversalTensorSquare.sg37618`, `OAI.UniversalTensorSquare.sg37622`, `OAI.UniversalTensorSquare.sg37625`, `OAI.UniversalTensorSquare.sg37627`, `OAI.UniversalTensorSquare.sg38360`, `OAI.UniversalTensorSquare.sg38367`, `OAI.UniversalTensorSquare.sg38368`, `OAI.UniversalTensorSquare.sg38703`, `OAI.UniversalTensorSquare.sg38707`, `OAI.UniversalTensorSquare.sg38710`, `OAI.UniversalTensorSquare.sg38712`, `OAI.UniversalTensorSquare.sg38758`, `OAI.UniversalTensorSquare.sg38825`, `OAI.UniversalTensorSquare.sg38829`, `OAI.UniversalTensorSquare.sg38832`, `OAI.UniversalTensorSquare.sg38834`, `OAI.UniversalTensorSquare.sg39473`, `OAI.UniversalTensorSquare.sg39477`, `OAI.UniversalTensorSquare.sg39480`, `OAI.UniversalTensorSquare.sg39481`, `OAI.UniversalTensorSquare.sg40749`, `OAI.UniversalTensorSquare.sg40758`, `OAI.UniversalTensorSquare.sg40760`, `OAI.UniversalTensorSquare.sg40761`, `OAI.UniversalTensorSquare.sg40774`, `OAI.UniversalTensorSquare.sg41164`, `OAI.UniversalTensorSquare.sg41168`, `OAI.UniversalTensorSquare.sg41170`, `OAI.UniversalTensorSquare.sg41171`, `OAI.UniversalTensorSquare.sg42763`, `OAI.UniversalTensorSquare.sg42833`, `OAI.UniversalTensorSquare.sg42834`, `OAI.UniversalTensorSquare.sg42911`, `OAI.UniversalTensorSquare.sg42912`, `OAI.UniversalTensorSquare.sg42973`, `OAI.UniversalTensorSquare.sg42974`, `OAI.UniversalTensorSquare.sg42995`, `OAI.UniversalTensorSquare.sg42996`, `OAI.UniversalTensorSquare.sg43080`, `OAI.UniversalTensorSquare.sg43081`, `OAI.UniversalTensorSquare.sg43123`, `OAI.UniversalTensorSquare.sg43137`, `OAI.UniversalTensorSquare.sg43174`, `OAI.UniversalTensorSquare.sg43185`, `OAI.UniversalTensorSquare.sg43196`, `OAI.UniversalTensorSquare.sg6310`, `OAI.UniversalTensorSquare.sg7247`, `OAI.UniversalTensorSquare.sg7252`, `OAI.UniversalTensorSquare.sg841` and `OAI.UniversalTensorSquare.sg9247` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean (declaration OAI.UniversalTensorSquare.sgCert841)

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

lemma sgCert841 : solveCompact 10 (.full [5,5]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB841 sgT841) sgFlag841 = -2 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
