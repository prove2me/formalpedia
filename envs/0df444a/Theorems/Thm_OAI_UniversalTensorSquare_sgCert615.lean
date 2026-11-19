-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert615
-- name    : OAI.UniversalTensorSquare.sgCert615
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:19:02.764372+00:00
-- url     : https://prove2.me/theorems/10bf1753-9b40-4f44-9b68-be1560047db6
-- title:
--   OAI.UniversalTensorSquare.sgCert615: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert615` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert615 : solveCompact 9 (.full [6,3]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
--       (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [6,3] (Equiv.refl (Fin 9)) sgB615 sgT615) sgFlag615 = 13
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB615` and `OAI.UniversalTensorSquare.sgFlag615` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT615` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_619All`, `OAI.UniversalTensorSquare.sg16497`, `OAI.UniversalTensorSquare.sg16677`, `OAI.UniversalTensorSquare.sg16715`, `OAI.UniversalTensorSquare.sg17617`, `OAI.UniversalTensorSquare.sg21777`, `OAI.UniversalTensorSquare.sg21803`, `OAI.UniversalTensorSquare.sg21817`, `OAI.UniversalTensorSquare.sg21883`, `OAI.UniversalTensorSquare.sg21887`, `OAI.UniversalTensorSquare.sg34775`, `OAI.UniversalTensorSquare.sg34880`, `OAI.UniversalTensorSquare.sg34892`, `OAI.UniversalTensorSquare.sg34894`, `OAI.UniversalTensorSquare.sg34896`, `OAI.UniversalTensorSquare.sg34898`, `OAI.UniversalTensorSquare.sg34941`, `OAI.UniversalTensorSquare.sg35003`, `OAI.UniversalTensorSquare.sg35004`, `OAI.UniversalTensorSquare.sg35005`, `OAI.UniversalTensorSquare.sg35051`, `OAI.UniversalTensorSquare.sg35052`, `OAI.UniversalTensorSquare.sg35053`, `OAI.UniversalTensorSquare.sg42386`, `OAI.UniversalTensorSquare.sg42387`, `OAI.UniversalTensorSquare.sg615`, `OAI.UniversalTensorSquare.sg6798`, `OAI.UniversalTensorSquare.sg6821`, `OAI.UniversalTensorSquare.sg8489`, `OAI.UniversalTensorSquare.sg9937`, `OAI.UniversalTensorSquare.sg9945` and `OAI.UniversalTensorSquare.sg9999` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean (declaration OAI.UniversalTensorSquare.sgCert615)

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

lemma sgCert615 : solveCompact 9 (.full [6,3]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
    (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [6,3] (Equiv.refl (Fin 9)) sgB615 sgT615) sgFlag615 = 13 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
