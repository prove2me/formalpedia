-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert1033
-- name    : OAI.UniversalTensorSquare.sgCert1033
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T00:13:37.045774+00:00
-- url     : https://prove2.me/theorems/1af5a7d3-8e3f-48da-bc4a-0643b15a7c23
-- title:
--   OAI.UniversalTensorSquare.sgCert1033: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert1033` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert1033 : solveCompact 10 (.full [5,5]) (.full [4,2,1,1,1,1]) (.full [4,2,1,1,1,1])
--       (certificateEdges [4,2,1,1,1,1] [4,2,1,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB1033 sgT1033) sgFlag1033 = -12
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB1033` and `OAI.UniversalTensorSquare.sgFlag1033` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT1033` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg10006`, `OAI.UniversalTensorSquare.sg1033`, `OAI.UniversalTensorSquare.sg16699`, `OAI.UniversalTensorSquare.sg18038`, `OAI.UniversalTensorSquare.sg19330`, `OAI.UniversalTensorSquare.sg20175`, `OAI.UniversalTensorSquare.sg27499`, `OAI.UniversalTensorSquare.sg34025`, `OAI.UniversalTensorSquare.sg34028`, `OAI.UniversalTensorSquare.sg35456`, `OAI.UniversalTensorSquare.sg35597`, `OAI.UniversalTensorSquare.sg35599`, `OAI.UniversalTensorSquare.sg35601`, `OAI.UniversalTensorSquare.sg35819`, `OAI.UniversalTensorSquare.sg35821`, `OAI.UniversalTensorSquare.sg35823`, `OAI.UniversalTensorSquare.sg36145`, `OAI.UniversalTensorSquare.sg36207`, `OAI.UniversalTensorSquare.sg36539`, `OAI.UniversalTensorSquare.sg36541`, `OAI.UniversalTensorSquare.sg36543`, `OAI.UniversalTensorSquare.sg36786`, `OAI.UniversalTensorSquare.sg36887`, `OAI.UniversalTensorSquare.sg37011`, `OAI.UniversalTensorSquare.sg37021`, `OAI.UniversalTensorSquare.sg37024`, `OAI.UniversalTensorSquare.sg37026`, `OAI.UniversalTensorSquare.sg37486`, `OAI.UniversalTensorSquare.sg37590`, `OAI.UniversalTensorSquare.sg38014`, `OAI.UniversalTensorSquare.sg38016`, `OAI.UniversalTensorSquare.sg38018`, `OAI.UniversalTensorSquare.sg38238`, `OAI.UniversalTensorSquare.sg38241`, `OAI.UniversalTensorSquare.sg38243`, `OAI.UniversalTensorSquare.sg38517`, `OAI.UniversalTensorSquare.sg38559`, `OAI.UniversalTensorSquare.sg38569`, `OAI.UniversalTensorSquare.sg38572`, `OAI.UniversalTensorSquare.sg38574`, `OAI.UniversalTensorSquare.sg38662`, `OAI.UniversalTensorSquare.sg38664`, `OAI.UniversalTensorSquare.sg38667`, `OAI.UniversalTensorSquare.sg38670`, `OAI.UniversalTensorSquare.sg38706`, `OAI.UniversalTensorSquare.sg38709`, `OAI.UniversalTensorSquare.sg39016`, `OAI.UniversalTensorSquare.sg39018`, `OAI.UniversalTensorSquare.sg39020`, `OAI.UniversalTensorSquare.sg39297`, `OAI.UniversalTensorSquare.sg39303`, `OAI.UniversalTensorSquare.sg39306`, `OAI.UniversalTensorSquare.sg39441`, `OAI.UniversalTensorSquare.sg39444`, `OAI.UniversalTensorSquare.sg39476`, `OAI.UniversalTensorSquare.sg39479`, `OAI.UniversalTensorSquare.sg39683`, `OAI.UniversalTensorSquare.sg39686`, `OAI.UniversalTensorSquare.sg39718`, `OAI.UniversalTensorSquare.sg39721`, `OAI.UniversalTensorSquare.sg39902`, `OAI.UniversalTensorSquare.sg39905`, `OAI.UniversalTensorSquare.sg40020`, `OAI.UniversalTensorSquare.sg40022`, `OAI.UniversalTensorSquare.sg40023`, `OAI.UniversalTensorSquare.sg40330`, `OAI.UniversalTensorSquare.sg40332`, `OAI.UniversalTensorSquare.sg40333`, `OAI.UniversalTensorSquare.sg40878`, `OAI.UniversalTensorSquare.sg40880`, `OAI.UniversalTensorSquare.sg40881`, `OAI.UniversalTensorSquare.sg41104`, `OAI.UniversalTensorSquare.sg41355`, `OAI.UniversalTensorSquare.sg41799`, `OAI.UniversalTensorSquare.sg41801`, `OAI.UniversalTensorSquare.sg41923`, `OAI.UniversalTensorSquare.sg42052`, `OAI.UniversalTensorSquare.sg42068`, `OAI.UniversalTensorSquare.sg42076`, `OAI.UniversalTensorSquare.sg42167`, `OAI.UniversalTensorSquare.sg42168`, `OAI.UniversalTensorSquare.sg42169`, `OAI.UniversalTensorSquare.sg42230`, `OAI.UniversalTensorSquare.sg42231`, `OAI.UniversalTensorSquare.sg42272`, `OAI.UniversalTensorSquare.sg42292`, `OAI.UniversalTensorSquare.sg42332`, `OAI.UniversalTensorSquare.sg42333`, `OAI.UniversalTensorSquare.sg42337`, `OAI.UniversalTensorSquare.sg42398`, `OAI.UniversalTensorSquare.sg42399`, `OAI.UniversalTensorSquare.sg42438`, `OAI.UniversalTensorSquare.sg42439`, `OAI.UniversalTensorSquare.sg42477`, `OAI.UniversalTensorSquare.sg42478`, `OAI.UniversalTensorSquare.sg42499`, `OAI.UniversalTensorSquare.sg42618`, `OAI.UniversalTensorSquare.sg42619`, `OAI.UniversalTensorSquare.sg42633`, `OAI.UniversalTensorSquare.sg42634`, `OAI.UniversalTensorSquare.sg42726`, `OAI.UniversalTensorSquare.sg42727`, `OAI.UniversalTensorSquare.sg43133`, `OAI.UniversalTensorSquare.sg43156`, `OAI.UniversalTensorSquare.sg43231`, `OAI.UniversalTensorSquare.sg5439`, `OAI.UniversalTensorSquare.sg5860`, `OAI.UniversalTensorSquare.sg5864`, `OAI.UniversalTensorSquare.sg6642`, `OAI.UniversalTensorSquare.sg6682`, `OAI.UniversalTensorSquare.sg6684`, `OAI.UniversalTensorSquare.sg6689`, `OAI.UniversalTensorSquare.sg6788`, `OAI.UniversalTensorSquare.sg6823`, `OAI.UniversalTensorSquare.sg7188`, `OAI.UniversalTensorSquare.sg7199`, `OAI.UniversalTensorSquare.sg7307`, `OAI.UniversalTensorSquare.sg7315`, `OAI.UniversalTensorSquare.sg7357`, `OAI.UniversalTensorSquare.sg7359`, `OAI.UniversalTensorSquare.sg7389`, `OAI.UniversalTensorSquare.sg9095`, `OAI.UniversalTensorSquare.sg9255`, `OAI.UniversalTensorSquare.sg9259`, `OAI.UniversalTensorSquare.sg9329`, `OAI.UniversalTensorSquare.sg9350`, `OAI.UniversalTensorSquare.sg9359`, `OAI.UniversalTensorSquare.sg9461`, `OAI.UniversalTensorSquare.sg9506`, `OAI.UniversalTensorSquare.sg9528`, `OAI.UniversalTensorSquare.sg9554`, `OAI.UniversalTensorSquare.sg9578`, `OAI.UniversalTensorSquare.sg9619`, `OAI.UniversalTensorSquare.sg9626`, `OAI.UniversalTensorSquare.sg9803`, `OAI.UniversalTensorSquare.sg9832`, `OAI.UniversalTensorSquare.sg9841`, `OAI.UniversalTensorSquare.sg9843`, `OAI.UniversalTensorSquare.sg9907` and `OAI.UniversalTensorSquare.sg9933` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean (declaration OAI.UniversalTensorSquare.sgCert1033)

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

lemma sgCert1033 : solveCompact 10 (.full [5,5]) (.full [4,2,1,1,1,1]) (.full [4,2,1,1,1,1])
    (certificateEdges [4,2,1,1,1,1] [4,2,1,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB1033 sgT1033) sgFlag1033 = -12 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
