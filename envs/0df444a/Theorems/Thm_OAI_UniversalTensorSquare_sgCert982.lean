-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert982
-- name    : OAI.UniversalTensorSquare.sgCert982
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:48:07.71322+00:00
-- url     : https://prove2.me/theorems/72d7c81e-548e-4ea9-8a7a-92191f41cfcd
-- title:
--   OAI.UniversalTensorSquare.sgCert982: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert982` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert982 : solveCompact 10 (.full [5,5]) (.full [3,2,2,2,1]) (.full [3,2,2,2,1])
--       (certificateEdges [3,2,2,2,1] [3,2,2,2,1] [5,5] (Equiv.refl (Fin 10)) sgB982 sgT982) sgFlag982 = 99
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB982` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgFlag982` and `OAI.UniversalTensorSquare.sgT982` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg36277`, `OAI.UniversalTensorSquare.sg36287`, `OAI.UniversalTensorSquare.sg36290`, `OAI.UniversalTensorSquare.sg36292`, `OAI.UniversalTensorSquare.sg36886`, `OAI.UniversalTensorSquare.sg36889`, `OAI.UniversalTensorSquare.sg36891`, `OAI.UniversalTensorSquare.sg37568`, `OAI.UniversalTensorSquare.sg37578`, `OAI.UniversalTensorSquare.sg37581`, `OAI.UniversalTensorSquare.sg37583`, `OAI.UniversalTensorSquare.sg37618`, `OAI.UniversalTensorSquare.sg37622`, `OAI.UniversalTensorSquare.sg37625`, `OAI.UniversalTensorSquare.sg37627`, `OAI.UniversalTensorSquare.sg39083`, `OAI.UniversalTensorSquare.sg39086`, `OAI.UniversalTensorSquare.sg39088`, `OAI.UniversalTensorSquare.sg39294`, `OAI.UniversalTensorSquare.sg39304`, `OAI.UniversalTensorSquare.sg39307`, `OAI.UniversalTensorSquare.sg39308`, `OAI.UniversalTensorSquare.sg39432`, `OAI.UniversalTensorSquare.sg39442`, `OAI.UniversalTensorSquare.sg39445`, `OAI.UniversalTensorSquare.sg39446`, `OAI.UniversalTensorSquare.sg39473`, `OAI.UniversalTensorSquare.sg39477`, `OAI.UniversalTensorSquare.sg39480`, `OAI.UniversalTensorSquare.sg39481`, `OAI.UniversalTensorSquare.sg40676`, `OAI.UniversalTensorSquare.sg40678`, `OAI.UniversalTensorSquare.sg40679`, `OAI.UniversalTensorSquare.sg40905`, `OAI.UniversalTensorSquare.sg40916`, `OAI.UniversalTensorSquare.sg40917`, `OAI.UniversalTensorSquare.sg40918`, `OAI.UniversalTensorSquare.sg41315`, `OAI.UniversalTensorSquare.sg41755`, `OAI.UniversalTensorSquare.sg42906`, `OAI.UniversalTensorSquare.sg43122`, `OAI.UniversalTensorSquare.sg43136`, `OAI.UniversalTensorSquare.sg43143`, `OAI.UniversalTensorSquare.sg43167`, `OAI.UniversalTensorSquare.sg43168`, `OAI.UniversalTensorSquare.sg43178`, `OAI.UniversalTensorSquare.sg8040`, `OAI.UniversalTensorSquare.sg8047`, `OAI.UniversalTensorSquare.sg8064`, `OAI.UniversalTensorSquare.sg8067` and `OAI.UniversalTensorSquare.sg982` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean (declaration OAI.UniversalTensorSquare.sgCert982)

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

lemma sgCert982 : solveCompact 10 (.full [5,5]) (.full [3,2,2,2,1]) (.full [3,2,2,2,1])
    (certificateEdges [3,2,2,2,1] [3,2,2,2,1] [5,5] (Equiv.refl (Fin 10)) sgB982 sgT982) sgFlag982 = 99 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
