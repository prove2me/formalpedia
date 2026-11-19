-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert892
-- name    : OAI.UniversalTensorSquare.sgCert892
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:40:28.701091+00:00
-- url     : https://prove2.me/theorems/69d3d257-c5ba-4708-93b6-0445f929597e
-- title:
--   OAI.UniversalTensorSquare.sgCert892: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert892` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert892 : solveCompact 10 (.full [5,5]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
--       (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB892 sgT892) sgFlag892 = 1440
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB892` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgFlag892` and `OAI.UniversalTensorSquare.sgT892` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg24215`, `OAI.UniversalTensorSquare.sg25657`, `OAI.UniversalTensorSquare.sg35376`, `OAI.UniversalTensorSquare.sg35465`, `OAI.UniversalTensorSquare.sg36286`, `OAI.UniversalTensorSquare.sg36289`, `OAI.UniversalTensorSquare.sg36590`, `OAI.UniversalTensorSquare.sg36592`, `OAI.UniversalTensorSquare.sg36981`, `OAI.UniversalTensorSquare.sg37020`, `OAI.UniversalTensorSquare.sg37023`, `OAI.UniversalTensorSquare.sg37030`, `OAI.UniversalTensorSquare.sg37311`, `OAI.UniversalTensorSquare.sg37483`, `OAI.UniversalTensorSquare.sg37668`, `OAI.UniversalTensorSquare.sg37958`, `OAI.UniversalTensorSquare.sg38342`, `OAI.UniversalTensorSquare.sg38345`, `OAI.UniversalTensorSquare.sg38355`, `OAI.UniversalTensorSquare.sg38748`, `OAI.UniversalTensorSquare.sg40205`, `OAI.UniversalTensorSquare.sg4027`, `OAI.UniversalTensorSquare.sg4199`, `OAI.UniversalTensorSquare.sg4379`, `OAI.UniversalTensorSquare.sg4423`, `OAI.UniversalTensorSquare.sg4426`, `OAI.UniversalTensorSquare.sg4901`, `OAI.UniversalTensorSquare.sg4905`, `OAI.UniversalTensorSquare.sg7312`, `OAI.UniversalTensorSquare.sg7315`, `OAI.UniversalTensorSquare.sg7350`, `OAI.UniversalTensorSquare.sg7583`, `OAI.UniversalTensorSquare.sg892` and `OAI.UniversalTensorSquare.sg9530` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean (declaration OAI.UniversalTensorSquare.sgCert892)

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

lemma sgCert892 : solveCompact 10 (.full [5,5]) (.full [5,1,1,1,1,1]) (.full [5,1,1,1,1,1])
    (certificateEdges [5,1,1,1,1,1] [5,1,1,1,1,1] [5,5] (Equiv.refl (Fin 10)) sgB892 sgT892) sgFlag892 = 1440 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
