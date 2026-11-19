-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert564
-- name    : OAI.UniversalTensorSquare.sgCert564
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:17:54.075193+00:00
-- url     : https://prove2.me/theorems/f72d0ae6-0d37-41a6-b38b-e1021eb3e8de
-- title:
--   OAI.UniversalTensorSquare.sgCert564: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert564` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert564 : solveCompact 9 (.full [5,4]) (.full [4,2,2,1]) (.full [4,2,2,1])
--       (certificateEdges [4,2,2,1] [4,2,2,1] [5,4] (Equiv.refl (Fin 9)) sgB564 sgT564) sgFlag564 = 7
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB564` and `OAI.UniversalTensorSquare.sgFlag564` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT564` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg13817`, `OAI.UniversalTensorSquare.sg27245`, `OAI.UniversalTensorSquare.sg28053`, `OAI.UniversalTensorSquare.sg34402`, `OAI.UniversalTensorSquare.sg34545`, `OAI.UniversalTensorSquare.sg34571`, `OAI.UniversalTensorSquare.sg34595`, `OAI.UniversalTensorSquare.sg35323`, `OAI.UniversalTensorSquare.sg35325`, `OAI.UniversalTensorSquare.sg35326`, `OAI.UniversalTensorSquare.sg35328`, `OAI.UniversalTensorSquare.sg35330`, `OAI.UniversalTensorSquare.sg35332`, `OAI.UniversalTensorSquare.sg35439`, `OAI.UniversalTensorSquare.sg37629`, `OAI.UniversalTensorSquare.sg37633`, `OAI.UniversalTensorSquare.sg37636`, `OAI.UniversalTensorSquare.sg38322`, `OAI.UniversalTensorSquare.sg38323`, `OAI.UniversalTensorSquare.sg38875`, `OAI.UniversalTensorSquare.sg39433`, `OAI.UniversalTensorSquare.sg40732` and `OAI.UniversalTensorSquare.sg564` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean (declaration OAI.UniversalTensorSquare.sgCert564)

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

lemma sgCert564 : solveCompact 9 (.full [5,4]) (.full [4,2,2,1]) (.full [4,2,2,1])
    (certificateEdges [4,2,2,1] [4,2,2,1] [5,4] (Equiv.refl (Fin 9)) sgB564 sgT564) sgFlag564 = 7 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
