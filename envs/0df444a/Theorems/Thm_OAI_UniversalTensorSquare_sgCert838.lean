-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert838
-- name    : OAI.UniversalTensorSquare.sgCert838
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:31:23.111972+00:00
-- url     : https://prove2.me/theorems/4c2e8eb3-4a00-46df-afc6-0ed31403af41
-- title:
--   OAI.UniversalTensorSquare.sgCert838: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert838` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert838 : solveCompact 10 (.full [8,2]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
--       (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [8,2] (Equiv.refl (Fin 10)) sgB838 sgT838) sgFlag838 = -16
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB838` and `OAI.UniversalTensorSquare.sgFlag838` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT838` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_45All`, `OAI.UniversalTensorSquare.degreeTree43_221All`, `OAI.UniversalTensorSquare.sg13163`, `OAI.UniversalTensorSquare.sg13340`, `OAI.UniversalTensorSquare.sg19161`, `OAI.UniversalTensorSquare.sg35508`, `OAI.UniversalTensorSquare.sg35510`, `OAI.UniversalTensorSquare.sg36400`, `OAI.UniversalTensorSquare.sg36402`, `OAI.UniversalTensorSquare.sg36779`, `OAI.UniversalTensorSquare.sg36782`, `OAI.UniversalTensorSquare.sg36784`, `OAI.UniversalTensorSquare.sg36798`, `OAI.UniversalTensorSquare.sg36864`, `OAI.UniversalTensorSquare.sg36867`, `OAI.UniversalTensorSquare.sg36869`, `OAI.UniversalTensorSquare.sg36886`, `OAI.UniversalTensorSquare.sg36889`, `OAI.UniversalTensorSquare.sg36891`, `OAI.UniversalTensorSquare.sg37821`, `OAI.UniversalTensorSquare.sg37824`, `OAI.UniversalTensorSquare.sg37826`, `OAI.UniversalTensorSquare.sg38092`, `OAI.UniversalTensorSquare.sg38095`, `OAI.UniversalTensorSquare.sg38097`, `OAI.UniversalTensorSquare.sg38174`, `OAI.UniversalTensorSquare.sg38211`, `OAI.UniversalTensorSquare.sg38214`, `OAI.UniversalTensorSquare.sg38216`, `OAI.UniversalTensorSquare.sg38392`, `OAI.UniversalTensorSquare.sg38395`, `OAI.UniversalTensorSquare.sg38397`, `OAI.UniversalTensorSquare.sg38413`, `OAI.UniversalTensorSquare.sg38416`, `OAI.UniversalTensorSquare.sg38418`, `OAI.UniversalTensorSquare.sg38967`, `OAI.UniversalTensorSquare.sg38970`, `OAI.UniversalTensorSquare.sg38972`, `OAI.UniversalTensorSquare.sg39024`, `OAI.UniversalTensorSquare.sg39027`, `OAI.UniversalTensorSquare.sg39029`, `OAI.UniversalTensorSquare.sg39070`, `OAI.UniversalTensorSquare.sg39072`, `OAI.UniversalTensorSquare.sg39083`, `OAI.UniversalTensorSquare.sg39086`, `OAI.UniversalTensorSquare.sg39088`, `OAI.UniversalTensorSquare.sg39191`, `OAI.UniversalTensorSquare.sg39194`, `OAI.UniversalTensorSquare.sg39196`, `OAI.UniversalTensorSquare.sg39210`, `OAI.UniversalTensorSquare.sg39213`, `OAI.UniversalTensorSquare.sg39215`, `OAI.UniversalTensorSquare.sg39548`, `OAI.UniversalTensorSquare.sg39551`, `OAI.UniversalTensorSquare.sg39552`, `OAI.UniversalTensorSquare.sg40027`, `OAI.UniversalTensorSquare.sg40029`, `OAI.UniversalTensorSquare.sg40030`, `OAI.UniversalTensorSquare.sg40061`, `OAI.UniversalTensorSquare.sg40063`, `OAI.UniversalTensorSquare.sg40064`, `OAI.UniversalTensorSquare.sg40076`, `OAI.UniversalTensorSquare.sg40078`, `OAI.UniversalTensorSquare.sg40079`, `OAI.UniversalTensorSquare.sg40089`, `OAI.UniversalTensorSquare.sg40091`, `OAI.UniversalTensorSquare.sg40092`, `OAI.UniversalTensorSquare.sg40482`, `OAI.UniversalTensorSquare.sg40484`, `OAI.UniversalTensorSquare.sg40485`, `OAI.UniversalTensorSquare.sg40908`, `OAI.UniversalTensorSquare.sg40910`, `OAI.UniversalTensorSquare.sg40911`, `OAI.UniversalTensorSquare.sg41533`, `OAI.UniversalTensorSquare.sg41535`, `OAI.UniversalTensorSquare.sg41544`, `OAI.UniversalTensorSquare.sg41546`, `OAI.UniversalTensorSquare.sg42675`, `OAI.UniversalTensorSquare.sg42861`, `OAI.UniversalTensorSquare.sg42875`, `OAI.UniversalTensorSquare.sg42889`, `OAI.UniversalTensorSquare.sg43033`, `OAI.UniversalTensorSquare.sg43048`, `OAI.UniversalTensorSquare.sg43060`, `OAI.UniversalTensorSquare.sg43097`, `OAI.UniversalTensorSquare.sg43108`, `OAI.UniversalTensorSquare.sg43127`, `OAI.UniversalTensorSquare.sg5715`, `OAI.UniversalTensorSquare.sg6305`, `OAI.UniversalTensorSquare.sg6868`, `OAI.UniversalTensorSquare.sg6872`, `OAI.UniversalTensorSquare.sg6874`, `OAI.UniversalTensorSquare.sg7897`, `OAI.UniversalTensorSquare.sg7899`, `OAI.UniversalTensorSquare.sg7913`, `OAI.UniversalTensorSquare.sg7916`, `OAI.UniversalTensorSquare.sg7921`, `OAI.UniversalTensorSquare.sg7926`, `OAI.UniversalTensorSquare.sg7929`, `OAI.UniversalTensorSquare.sg7943`, `OAI.UniversalTensorSquare.sg7954`, `OAI.UniversalTensorSquare.sg7957`, `OAI.UniversalTensorSquare.sg7963`, `OAI.UniversalTensorSquare.sg7965`, `OAI.UniversalTensorSquare.sg7967`, `OAI.UniversalTensorSquare.sg7968`, `OAI.UniversalTensorSquare.sg7978`, `OAI.UniversalTensorSquare.sg7983`, `OAI.UniversalTensorSquare.sg838`, `OAI.UniversalTensorSquare.sg8665` and `OAI.UniversalTensorSquare.sg9240` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean (declaration OAI.UniversalTensorSquare.sgCert838)

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

lemma sgCert838 : solveCompact 10 (.full [8,2]) (.full [4,3,1,1,1]) (.full [4,3,1,1,1])
    (certificateEdges [4,3,1,1,1] [4,3,1,1,1] [8,2] (Equiv.refl (Fin 10)) sgB838 sgT838) sgFlag838 = -16 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
