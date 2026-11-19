-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert356
-- name    : OAI.UniversalTensorSquare.sgCert356
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:08:02.939601+00:00
-- url     : https://prove2.me/theorems/a1a69719-4e03-4140-b0fa-ee9f3f9c76a8
-- title:
--   OAI.UniversalTensorSquare.sgCert356: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert356` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert356 : solveCompact 8 (.full [6,2]) (.full [3,2,2,1]) (.full [3,2,2,1])
--       (certificateEdges [3,2,2,1] [3,2,2,1] [6,2] (Equiv.refl (Fin 8)) sgB356 sgT356) sgFlag356 = 12
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB356` and `OAI.UniversalTensorSquare.sgFlag356` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT356` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_260All`, `OAI.UniversalTensorSquare.sg15533`, `OAI.UniversalTensorSquare.sg23564`, `OAI.UniversalTensorSquare.sg23571`, `OAI.UniversalTensorSquare.sg23577`, `OAI.UniversalTensorSquare.sg27000`, `OAI.UniversalTensorSquare.sg27041`, `OAI.UniversalTensorSquare.sg27069`, `OAI.UniversalTensorSquare.sg27077`, `OAI.UniversalTensorSquare.sg27084`, `OAI.UniversalTensorSquare.sg29991`, `OAI.UniversalTensorSquare.sg31135`, `OAI.UniversalTensorSquare.sg31143`, `OAI.UniversalTensorSquare.sg31150`, `OAI.UniversalTensorSquare.sg356`, `OAI.UniversalTensorSquare.sg39164`, `OAI.UniversalTensorSquare.sg40177`, `OAI.UniversalTensorSquare.sg40897`, `OAI.UniversalTensorSquare.sg40898`, `OAI.UniversalTensorSquare.sg40899`, `OAI.UniversalTensorSquare.sg41024`, `OAI.UniversalTensorSquare.sg41025`, `OAI.UniversalTensorSquare.sg41026`, `OAI.UniversalTensorSquare.sg41098`, `OAI.UniversalTensorSquare.sg41725`, `OAI.UniversalTensorSquare.sg41932`, `OAI.UniversalTensorSquare.sg41983`, `OAI.UniversalTensorSquare.sg42034`, `OAI.UniversalTensorSquare.sg42042`, `OAI.UniversalTensorSquare.sg42688` and `OAI.UniversalTensorSquare.sg42751` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean (declaration OAI.UniversalTensorSquare.sgCert356)

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

lemma sgCert356 : solveCompact 8 (.full [6,2]) (.full [3,2,2,1]) (.full [3,2,2,1])
    (certificateEdges [3,2,2,1] [3,2,2,1] [6,2] (Equiv.refl (Fin 8)) sgB356 sgT356) sgFlag356 = 12 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
