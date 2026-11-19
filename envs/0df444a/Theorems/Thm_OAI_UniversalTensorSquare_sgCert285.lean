-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert285
-- name    : OAI.UniversalTensorSquare.sgCert285
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T00:19:11.97327+00:00
-- url     : https://prove2.me/theorems/66c18059-5b4e-4bd6-aa0d-f80e425fe11d
-- title:
--   OAI.UniversalTensorSquare.sgCert285: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert285` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert285 : solveCompact 8 (.full [6,2]) (.full [3,2,2,1]) (.full [3,2,2,1])
--       (certificateEdges [3,2,2,1] [3,2,2,1] [6,2] (Equiv.refl (Fin 8)) sgB285 sgT285) sgFlag285 = 24
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB285` and `OAI.UniversalTensorSquare.sgFlag285` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT285` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_378All`, `OAI.UniversalTensorSquare.degreeTree62_742All`, `OAI.UniversalTensorSquare.sg23504`, `OAI.UniversalTensorSquare.sg24844`, `OAI.UniversalTensorSquare.sg24918`, `OAI.UniversalTensorSquare.sg26971`, `OAI.UniversalTensorSquare.sg27049`, `OAI.UniversalTensorSquare.sg27051`, `OAI.UniversalTensorSquare.sg27053`, `OAI.UniversalTensorSquare.sg30701`, `OAI.UniversalTensorSquare.sg35869`, `OAI.UniversalTensorSquare.sg36752`, `OAI.UniversalTensorSquare.sg37891`, `OAI.UniversalTensorSquare.sg37921`, `OAI.UniversalTensorSquare.sg37923`, `OAI.UniversalTensorSquare.sg38041`, `OAI.UniversalTensorSquare.sg38101`, `OAI.UniversalTensorSquare.sg38410`, `OAI.UniversalTensorSquare.sg38494`, `OAI.UniversalTensorSquare.sg39039`, `OAI.UniversalTensorSquare.sg39996`, `OAI.UniversalTensorSquare.sg40095`, `OAI.UniversalTensorSquare.sg40937`, `OAI.UniversalTensorSquare.sg41572`, `OAI.UniversalTensorSquare.sg41639`, `OAI.UniversalTensorSquare.sg42114`, `OAI.UniversalTensorSquare.sg42139` and `OAI.UniversalTensorSquare.sg42223` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean (declaration OAI.UniversalTensorSquare.sgCert285)

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

lemma sgCert285 : solveCompact 8 (.full [6,2]) (.full [3,2,2,1]) (.full [3,2,2,1])
    (certificateEdges [3,2,2,1] [3,2,2,1] [6,2] (Equiv.refl (Fin 8)) sgB285 sgT285) sgFlag285 = 24 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
