-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert915
-- name    : OAI.UniversalTensorSquare.sgCert915
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:40:47.350171+00:00
-- url     : https://prove2.me/theorems/97425bd3-03ec-4544-9567-6e6bc3674cef
-- title:
--   OAI.UniversalTensorSquare.sgCert915: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert915` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert915 : solveCompact 10 (.full [5,5]) (.full [5,2,1,1,1]) (.full [5,2,1,1,1])
--       (certificateEdges [5,2,1,1,1] [5,2,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB915 sgT915) sgFlag915 = -6
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB915` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgFlag915` and `OAI.UniversalTensorSquare.sgT915` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg16710`, `OAI.UniversalTensorSquare.sg34170`, `OAI.UniversalTensorSquare.sg34174`, `OAI.UniversalTensorSquare.sg34364`, `OAI.UniversalTensorSquare.sg34368`, `OAI.UniversalTensorSquare.sg34395`, `OAI.UniversalTensorSquare.sg34399`, `OAI.UniversalTensorSquare.sg34604`, `OAI.UniversalTensorSquare.sg34720`, `OAI.UniversalTensorSquare.sg35371`, `OAI.UniversalTensorSquare.sg35460`, `OAI.UniversalTensorSquare.sg36298`, `OAI.UniversalTensorSquare.sg36340`, `OAI.UniversalTensorSquare.sg36893`, `OAI.UniversalTensorSquare.sg36949`, `OAI.UniversalTensorSquare.sg36952`, `OAI.UniversalTensorSquare.sg37036`, `OAI.UniversalTensorSquare.sg37040`, `OAI.UniversalTensorSquare.sg37043`, `OAI.UniversalTensorSquare.sg38148`, `OAI.UniversalTensorSquare.sg38151`, `OAI.UniversalTensorSquare.sg38361`, `OAI.UniversalTensorSquare.sg38363`, `OAI.UniversalTensorSquare.sg38366`, `OAI.UniversalTensorSquare.sg38759`, `OAI.UniversalTensorSquare.sg38762`, `OAI.UniversalTensorSquare.sg38902`, `OAI.UniversalTensorSquare.sg38918`, `OAI.UniversalTensorSquare.sg38919`, `OAI.UniversalTensorSquare.sg39133`, `OAI.UniversalTensorSquare.sg39136`, `OAI.UniversalTensorSquare.sg39937`, `OAI.UniversalTensorSquare.sg40766`, `OAI.UniversalTensorSquare.sg40769`, `OAI.UniversalTensorSquare.sg40771`, `OAI.UniversalTensorSquare.sg41178`, `OAI.UniversalTensorSquare.sg41496`, `OAI.UniversalTensorSquare.sg41503`, `OAI.UniversalTensorSquare.sg41624`, `OAI.UniversalTensorSquare.sg41626`, `OAI.UniversalTensorSquare.sg42360`, `OAI.UniversalTensorSquare.sg4417`, `OAI.UniversalTensorSquare.sg4968`, `OAI.UniversalTensorSquare.sg6784`, `OAI.UniversalTensorSquare.sg6787`, `OAI.UniversalTensorSquare.sg6788`, `OAI.UniversalTensorSquare.sg7056`, `OAI.UniversalTensorSquare.sg7085`, `OAI.UniversalTensorSquare.sg8018`, `OAI.UniversalTensorSquare.sg8626`, `OAI.UniversalTensorSquare.sg915`, `OAI.UniversalTensorSquare.sg9170`, `OAI.UniversalTensorSquare.sg9727` and `OAI.UniversalTensorSquare.sg9835` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean (declaration OAI.UniversalTensorSquare.sgCert915)

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

lemma sgCert915 : solveCompact 10 (.full [5,5]) (.full [5,2,1,1,1]) (.full [5,2,1,1,1])
    (certificateEdges [5,2,1,1,1] [5,2,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB915 sgT915) sgFlag915 = -6 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
