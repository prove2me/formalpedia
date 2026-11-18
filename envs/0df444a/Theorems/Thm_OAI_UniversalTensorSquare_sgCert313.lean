-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert313
-- name    : OAI.UniversalTensorSquare.sgCert313
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-18T00:22:16.286889+00:00
-- url     : https://prove2.me/theorems/c87a1617-779c-4ef6-9b2c-6d6d60200d23
-- title:
--   OAI.UniversalTensorSquare.sgCert313: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert313` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert313 : solveCompact 8 (.full [6,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
--       (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [6,2] (Equiv.refl (Fin 8)) sgB313 sgT313) sgFlag313 = 24
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB313` and `OAI.UniversalTensorSquare.sgFlag313` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT313` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTreeAll41`, `OAI.UniversalTensorSquare.sg20165`, `OAI.UniversalTensorSquare.sg21795`, `OAI.UniversalTensorSquare.sg21824`, `OAI.UniversalTensorSquare.sg21933`, `OAI.UniversalTensorSquare.sg23639`, `OAI.UniversalTensorSquare.sg28854`, `OAI.UniversalTensorSquare.sg29315`, `OAI.UniversalTensorSquare.sg29530`, `OAI.UniversalTensorSquare.sg30820`, `OAI.UniversalTensorSquare.sg30887`, `OAI.UniversalTensorSquare.sg30958`, `OAI.UniversalTensorSquare.sg313`, `OAI.UniversalTensorSquare.sg31437`, `OAI.UniversalTensorSquare.sg35867`, `OAI.UniversalTensorSquare.sg36602`, `OAI.UniversalTensorSquare.sg36824`, `OAI.UniversalTensorSquare.sg36906`, `OAI.UniversalTensorSquare.sg36917`, `OAI.UniversalTensorSquare.sg36920`, `OAI.UniversalTensorSquare.sg37818`, `OAI.UniversalTensorSquare.sg37889`, `OAI.UniversalTensorSquare.sg37964`, `OAI.UniversalTensorSquare.sg38039`, `OAI.UniversalTensorSquare.sg38186`, `OAI.UniversalTensorSquare.sg38230`, `OAI.UniversalTensorSquare.sg38330`, `OAI.UniversalTensorSquare.sg38331`, `OAI.UniversalTensorSquare.sg38367`, `OAI.UniversalTensorSquare.sg38368`, `OAI.UniversalTensorSquare.sg38456`, `OAI.UniversalTensorSquare.sg38459`, `OAI.UniversalTensorSquare.sg38528`, `OAI.UniversalTensorSquare.sg38531`, `OAI.UniversalTensorSquare.sg39037`, `OAI.UniversalTensorSquare.sg39106`, `OAI.UniversalTensorSquare.sg39109`, `OAI.UniversalTensorSquare.sg39248`, `OAI.UniversalTensorSquare.sg39251`, `OAI.UniversalTensorSquare.sg39501`, `OAI.UniversalTensorSquare.sg39506`, `OAI.UniversalTensorSquare.sg39507`, `OAI.UniversalTensorSquare.sg39530`, `OAI.UniversalTensorSquare.sg39736`, `OAI.UniversalTensorSquare.sg39748`, `OAI.UniversalTensorSquare.sg39856`, `OAI.UniversalTensorSquare.sg40039`, `OAI.UniversalTensorSquare.sg40107`, `OAI.UniversalTensorSquare.sg40110`, `OAI.UniversalTensorSquare.sg40137`, `OAI.UniversalTensorSquare.sg40178`, `OAI.UniversalTensorSquare.sg40228`, `OAI.UniversalTensorSquare.sg41570`, `OAI.UniversalTensorSquare.sg41826`, `OAI.UniversalTensorSquare.sg42112`, `OAI.UniversalTensorSquare.sg42235`, `OAI.UniversalTensorSquare.sg42236`, `OAI.UniversalTensorSquare.sg42302`, `OAI.UniversalTensorSquare.sg42354`, `OAI.UniversalTensorSquare.sg42585`, `OAI.UniversalTensorSquare.sg42625`, `OAI.UniversalTensorSquare.sg42733`, `OAI.UniversalTensorSquare.sg42765`, `OAI.UniversalTensorSquare.sg7563`, `OAI.UniversalTensorSquare.sg9295`, `OAI.UniversalTensorSquare.sg9300`, `OAI.UniversalTensorSquare.sg9303`, `OAI.UniversalTensorSquare.sg9304`, `OAI.UniversalTensorSquare.sg9384`, `OAI.UniversalTensorSquare.sg9698`, `OAI.UniversalTensorSquare.sg9822` and `OAI.UniversalTensorSquare.sg9824` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean (declaration OAI.UniversalTensorSquare.sgCert313)

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

lemma sgCert313 : solveCompact 8 (.full [6,2]) (.full [4,1,1,1,1]) (.full [4,1,1,1,1])
    (certificateEdges [4,1,1,1,1] [4,1,1,1,1] [6,2] (Equiv.refl (Fin 8)) sgB313 sgT313) sgFlag313 = 24 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
