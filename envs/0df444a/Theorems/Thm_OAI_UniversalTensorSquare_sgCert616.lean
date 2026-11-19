-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert616
-- name    : OAI.UniversalTensorSquare.sgCert616
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:18:11.265923+00:00
-- url     : https://prove2.me/theorems/bbaf7420-d74a-49cc-ab68-611ca44539ae
-- title:
--   OAI.UniversalTensorSquare.sgCert616: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert616` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert616 : solveCompact 9 (.full [5,4]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
--       (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [5,4] (Equiv.refl (Fin 9)) sgB616 sgT616) sgFlag616 = 12
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB616` and `OAI.UniversalTensorSquare.sgFlag616` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT616` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg35284`, `OAI.UniversalTensorSquare.sg35372`, `OAI.UniversalTensorSquare.sg35461`, `OAI.UniversalTensorSquare.sg35470`, `OAI.UniversalTensorSquare.sg39059`, `OAI.UniversalTensorSquare.sg39061`, `OAI.UniversalTensorSquare.sg39063`, `OAI.UniversalTensorSquare.sg39497`, `OAI.UniversalTensorSquare.sg39498`, `OAI.UniversalTensorSquare.sg40657`, `OAI.UniversalTensorSquare.sg40659`, `OAI.UniversalTensorSquare.sg40660`, `OAI.UniversalTensorSquare.sg40677`, `OAI.UniversalTensorSquare.sg41360`, `OAI.UniversalTensorSquare.sg41773`, `OAI.UniversalTensorSquare.sg42994`, `OAI.UniversalTensorSquare.sg616`, `OAI.UniversalTensorSquare.sg6800`, `OAI.UniversalTensorSquare.sg6824` and `OAI.UniversalTensorSquare.sg6834` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean (declaration OAI.UniversalTensorSquare.sgCert616)

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

lemma sgCert616 : solveCompact 9 (.full [5,4]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
    (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [5,4] (Equiv.refl (Fin 9)) sgB616 sgT616) sgFlag616 = 12 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
