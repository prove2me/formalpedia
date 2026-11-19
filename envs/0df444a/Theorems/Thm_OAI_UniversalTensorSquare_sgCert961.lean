-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert961
-- name    : OAI.UniversalTensorSquare.sgCert961
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:47:45.004015+00:00
-- url     : https://prove2.me/theorems/89420a4d-ac46-45f0-95a5-d6d090d078b7
-- title:
--   OAI.UniversalTensorSquare.sgCert961: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert961` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert961 : solveCompact 10 (.full [5,5]) (.full [4,2,2,1,1]) (.full [4,2,2,1,1])
--       (certificateEdges [4,2,2,1,1] [4,2,2,1,1] [5,5] (Equiv.refl (Fin 10)) sgB961 sgT961) sgFlag961 = 4
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB961` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgFlag961` and `OAI.UniversalTensorSquare.sgT961` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg17527`, `OAI.UniversalTensorSquare.sg17609`, `OAI.UniversalTensorSquare.sg37111`, `OAI.UniversalTensorSquare.sg37113`, `OAI.UniversalTensorSquare.sg37115`, `OAI.UniversalTensorSquare.sg37680`, `OAI.UniversalTensorSquare.sg39508`, `OAI.UniversalTensorSquare.sg40581`, `OAI.UniversalTensorSquare.sg40583`, `OAI.UniversalTensorSquare.sg40584`, `OAI.UniversalTensorSquare.sg40969`, `OAI.UniversalTensorSquare.sg40971`, `OAI.UniversalTensorSquare.sg40972`, `OAI.UniversalTensorSquare.sg41559`, `OAI.UniversalTensorSquare.sg41561`, `OAI.UniversalTensorSquare.sg42105`, `OAI.UniversalTensorSquare.sg42164`, `OAI.UniversalTensorSquare.sg42275`, `OAI.UniversalTensorSquare.sg42276`, `OAI.UniversalTensorSquare.sg42579`, `OAI.UniversalTensorSquare.sg9425`, `OAI.UniversalTensorSquare.sg9493` and `OAI.UniversalTensorSquare.sg961` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean (declaration OAI.UniversalTensorSquare.sgCert961)

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

lemma sgCert961 : solveCompact 10 (.full [5,5]) (.full [4,2,2,1,1]) (.full [4,2,2,1,1])
    (certificateEdges [4,2,2,1,1] [4,2,2,1,1] [5,5] (Equiv.refl (Fin 10)) sgB961 sgT961) sgFlag961 = 4 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
