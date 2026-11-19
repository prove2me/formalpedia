-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert999
-- name    : OAI.UniversalTensorSquare.sgCert999
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:52:03.859164+00:00
-- url     : https://prove2.me/theorems/0b961656-2d59-4553-9bb5-c04bd51c8a2d
-- title:
--   OAI.UniversalTensorSquare.sgCert999: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert999` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert999 : solveCompact 10 (.full [7,3]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
--       (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [7,3] (Equiv.refl (Fin 10)) sgB999 sgT999) sgFlag999 = -48
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB999` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgFlag999` and `OAI.UniversalTensorSquare.sgT999` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_101All`, `OAI.UniversalTensorSquare.degreeTree62_833All`, `OAI.UniversalTensorSquare.degreeTree62_893All`, `OAI.UniversalTensorSquare.sg17455`, `OAI.UniversalTensorSquare.sg17457`, `OAI.UniversalTensorSquare.sg24132`, `OAI.UniversalTensorSquare.sg24284`, `OAI.UniversalTensorSquare.sg25583`, `OAI.UniversalTensorSquare.sg30328`, `OAI.UniversalTensorSquare.sg34652`, `OAI.UniversalTensorSquare.sg34781`, `OAI.UniversalTensorSquare.sg34841`, `OAI.UniversalTensorSquare.sg34901`, `OAI.UniversalTensorSquare.sg35164`, `OAI.UniversalTensorSquare.sg35181`, `OAI.UniversalTensorSquare.sg35540`, `OAI.UniversalTensorSquare.sg35542`, `OAI.UniversalTensorSquare.sg36773`, `OAI.UniversalTensorSquare.sg36775`, `OAI.UniversalTensorSquare.sg37251`, `OAI.UniversalTensorSquare.sg38499`, `OAI.UniversalTensorSquare.sg38501`, `OAI.UniversalTensorSquare.sg41230`, `OAI.UniversalTensorSquare.sg41307`, `OAI.UniversalTensorSquare.sg41856`, `OAI.UniversalTensorSquare.sg42932`, `OAI.UniversalTensorSquare.sg42943`, `OAI.UniversalTensorSquare.sg42944`, `OAI.UniversalTensorSquare.sg43049`, `OAI.UniversalTensorSquare.sg43050`, `OAI.UniversalTensorSquare.sg43093`, `OAI.UniversalTensorSquare.sg43094`, `OAI.UniversalTensorSquare.sg43115`, `OAI.UniversalTensorSquare.sg43149`, `OAI.UniversalTensorSquare.sg43155`, `OAI.UniversalTensorSquare.sg43208`, `OAI.UniversalTensorSquare.sg43211`, `OAI.UniversalTensorSquare.sg4487`, `OAI.UniversalTensorSquare.sg5420`, `OAI.UniversalTensorSquare.sg6773`, `OAI.UniversalTensorSquare.sg6915`, `OAI.UniversalTensorSquare.sg7082`, `OAI.UniversalTensorSquare.sg7088`, `OAI.UniversalTensorSquare.sg7095`, `OAI.UniversalTensorSquare.sg7152`, `OAI.UniversalTensorSquare.sg7228`, `OAI.UniversalTensorSquare.sg7317`, `OAI.UniversalTensorSquare.sg7579`, `OAI.UniversalTensorSquare.sg7585`, `OAI.UniversalTensorSquare.sg7587`, `OAI.UniversalTensorSquare.sg7650`, `OAI.UniversalTensorSquare.sg7654`, `OAI.UniversalTensorSquare.sg7712`, `OAI.UniversalTensorSquare.sg8446`, `OAI.UniversalTensorSquare.sg8535`, `OAI.UniversalTensorSquare.sg9220`, `OAI.UniversalTensorSquare.sg9267`, `OAI.UniversalTensorSquare.sg9277`, `OAI.UniversalTensorSquare.sg9285`, `OAI.UniversalTensorSquare.sg9287`, `OAI.UniversalTensorSquare.sg9300`, `OAI.UniversalTensorSquare.sg9319`, `OAI.UniversalTensorSquare.sg9559`, `OAI.UniversalTensorSquare.sg9565` and `OAI.UniversalTensorSquare.sg999` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean (declaration OAI.UniversalTensorSquare.sgCert999)

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

lemma sgCert999 : solveCompact 10 (.full [7,3]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [7,3] (Equiv.refl (Fin 10)) sgB999 sgT999) sgFlag999 = -48 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
