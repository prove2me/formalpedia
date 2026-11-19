-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert373
-- name    : OAI.UniversalTensorSquare.sgCert373
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:08:10.325302+00:00
-- url     : https://prove2.me/theorems/d8b0f88e-c367-439e-92e3-b28a8a0656c9
-- title:
--   OAI.UniversalTensorSquare.sgCert373: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert373` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert373 : solveCompact 8 (.full [4,4]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
--       (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [4,4] (Equiv.refl (Fin 8)) sgB373 sgT373) sgFlag373 = 24
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB373` and `OAI.UniversalTensorSquare.sgFlag373` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT373` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_277All`, `OAI.UniversalTensorSquare.degreeTree43_485All`, `OAI.UniversalTensorSquare.sg12148`, `OAI.UniversalTensorSquare.sg15867`, `OAI.UniversalTensorSquare.sg15939`, `OAI.UniversalTensorSquare.sg16727`, `OAI.UniversalTensorSquare.sg24570`, `OAI.UniversalTensorSquare.sg31312`, `OAI.UniversalTensorSquare.sg31336`, `OAI.UniversalTensorSquare.sg31340`, `OAI.UniversalTensorSquare.sg32562`, `OAI.UniversalTensorSquare.sg33249`, `OAI.UniversalTensorSquare.sg34097`, `OAI.UniversalTensorSquare.sg34279`, `OAI.UniversalTensorSquare.sg34288`, `OAI.UniversalTensorSquare.sg34343`, `OAI.UniversalTensorSquare.sg34460`, `OAI.UniversalTensorSquare.sg34472`, `OAI.UniversalTensorSquare.sg34475`, `OAI.UniversalTensorSquare.sg34476`, `OAI.UniversalTensorSquare.sg34477`, `OAI.UniversalTensorSquare.sg34554`, `OAI.UniversalTensorSquare.sg34706`, `OAI.UniversalTensorSquare.sg35117`, `OAI.UniversalTensorSquare.sg35118`, `OAI.UniversalTensorSquare.sg35119`, `OAI.UniversalTensorSquare.sg35124`, `OAI.UniversalTensorSquare.sg35139`, `OAI.UniversalTensorSquare.sg35143`, `OAI.UniversalTensorSquare.sg35166`, `OAI.UniversalTensorSquare.sg35168`, `OAI.UniversalTensorSquare.sg35260`, `OAI.UniversalTensorSquare.sg35263`, `OAI.UniversalTensorSquare.sg35265`, `OAI.UniversalTensorSquare.sg35274`, `OAI.UniversalTensorSquare.sg35278`, `OAI.UniversalTensorSquare.sg35280`, `OAI.UniversalTensorSquare.sg35288`, `OAI.UniversalTensorSquare.sg35290`, `OAI.UniversalTensorSquare.sg35294`, `OAI.UniversalTensorSquare.sg35310`, `OAI.UniversalTensorSquare.sg35323`, `OAI.UniversalTensorSquare.sg35325`, `OAI.UniversalTensorSquare.sg35326`, `OAI.UniversalTensorSquare.sg35328`, `OAI.UniversalTensorSquare.sg35330`, `OAI.UniversalTensorSquare.sg35332`, `OAI.UniversalTensorSquare.sg35338`, `OAI.UniversalTensorSquare.sg35382`, `OAI.UniversalTensorSquare.sg35384`, `OAI.UniversalTensorSquare.sg35391`, `OAI.UniversalTensorSquare.sg35404`, `OAI.UniversalTensorSquare.sg35410`, `OAI.UniversalTensorSquare.sg35426`, `OAI.UniversalTensorSquare.sg35439`, `OAI.UniversalTensorSquare.sg35446`, `OAI.UniversalTensorSquare.sg35456`, `OAI.UniversalTensorSquare.sg36119`, `OAI.UniversalTensorSquare.sg36852`, `OAI.UniversalTensorSquare.sg373`, `OAI.UniversalTensorSquare.sg37317`, `OAI.UniversalTensorSquare.sg37321`, `OAI.UniversalTensorSquare.sg37327`, `OAI.UniversalTensorSquare.sg37359`, `OAI.UniversalTensorSquare.sg37518`, `OAI.UniversalTensorSquare.sg37594`, `OAI.UniversalTensorSquare.sg37838`, `OAI.UniversalTensorSquare.sg37840`, `OAI.UniversalTensorSquare.sg38212`, `OAI.UniversalTensorSquare.sg38614`, `OAI.UniversalTensorSquare.sg38627`, `OAI.UniversalTensorSquare.sg38629`, `OAI.UniversalTensorSquare.sg38772`, `OAI.UniversalTensorSquare.sg38776`, `OAI.UniversalTensorSquare.sg38778`, `OAI.UniversalTensorSquare.sg38813`, `OAI.UniversalTensorSquare.sg3914`, `OAI.UniversalTensorSquare.sg39404`, `OAI.UniversalTensorSquare.sg39406`, `OAI.UniversalTensorSquare.sg39639`, `OAI.UniversalTensorSquare.sg39756`, `OAI.UniversalTensorSquare.sg39771`, `OAI.UniversalTensorSquare.sg39880`, `OAI.UniversalTensorSquare.sg39924`, `OAI.UniversalTensorSquare.sg41089`, `OAI.UniversalTensorSquare.sg41328`, `OAI.UniversalTensorSquare.sg41338`, `OAI.UniversalTensorSquare.sg41339`, `OAI.UniversalTensorSquare.sg41347`, `OAI.UniversalTensorSquare.sg41379`, `OAI.UniversalTensorSquare.sg41420`, `OAI.UniversalTensorSquare.sg41421`, `OAI.UniversalTensorSquare.sg41424`, `OAI.UniversalTensorSquare.sg41425`, `OAI.UniversalTensorSquare.sg41440`, `OAI.UniversalTensorSquare.sg41442`, `OAI.UniversalTensorSquare.sg41460`, `OAI.UniversalTensorSquare.sg41468`, `OAI.UniversalTensorSquare.sg41767`, `OAI.UniversalTensorSquare.sg41776`, `OAI.UniversalTensorSquare.sg41969`, `OAI.UniversalTensorSquare.sg41979`, `OAI.UniversalTensorSquare.sg41983`, `OAI.UniversalTensorSquare.sg42070`, `OAI.UniversalTensorSquare.sg42306`, `OAI.UniversalTensorSquare.sg42308`, `OAI.UniversalTensorSquare.sg42466`, `OAI.UniversalTensorSquare.sg42513`, `OAI.UniversalTensorSquare.sg42765`, `OAI.UniversalTensorSquare.sg42889`, `OAI.UniversalTensorSquare.sg42952`, `OAI.UniversalTensorSquare.sg42953`, `OAI.UniversalTensorSquare.sg42954`, `OAI.UniversalTensorSquare.sg42983`, `OAI.UniversalTensorSquare.sg42989`, `OAI.UniversalTensorSquare.sg42990`, `OAI.UniversalTensorSquare.sg42995`, `OAI.UniversalTensorSquare.sg42996`, `OAI.UniversalTensorSquare.sg43060`, `OAI.UniversalTensorSquare.sg43108`, `OAI.UniversalTensorSquare.sg43111`, `OAI.UniversalTensorSquare.sg43127`, `OAI.UniversalTensorSquare.sg43130`, `OAI.UniversalTensorSquare.sg43132`, `OAI.UniversalTensorSquare.sg43137`, `OAI.UniversalTensorSquare.sg43164`, `OAI.UniversalTensorSquare.sg43177`, `OAI.UniversalTensorSquare.sg43181`, `OAI.UniversalTensorSquare.sg43185`, `OAI.UniversalTensorSquare.sg43193`, `OAI.UniversalTensorSquare.sg43196`, `OAI.UniversalTensorSquare.sg5436`, `OAI.UniversalTensorSquare.sg5631`, `OAI.UniversalTensorSquare.sg5858`, `OAI.UniversalTensorSquare.sg7185`, `OAI.UniversalTensorSquare.sg7365`, `OAI.UniversalTensorSquare.sg7431`, `OAI.UniversalTensorSquare.sg8126`, `OAI.UniversalTensorSquare.sg9106`, `OAI.UniversalTensorSquare.sg9348`, `OAI.UniversalTensorSquare.sg9529`, `OAI.UniversalTensorSquare.sg9530`, `OAI.UniversalTensorSquare.sg9839`, `OAI.UniversalTensorSquare.sg9842`, `OAI.UniversalTensorSquare.sg9843`, `OAI.UniversalTensorSquare.sg9850`, `OAI.UniversalTensorSquare.sg9860`, `OAI.UniversalTensorSquare.sg9862`, `OAI.UniversalTensorSquare.sg9873`, `OAI.UniversalTensorSquare.sg9972` and `OAI.UniversalTensorSquare.sg9974` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean (declaration OAI.UniversalTensorSquare.sgCert373)

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

lemma sgCert373 : solveCompact 8 (.full [4,4]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [4,4] (Equiv.refl (Fin 8)) sgB373 sgT373) sgFlag373 = 24 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
