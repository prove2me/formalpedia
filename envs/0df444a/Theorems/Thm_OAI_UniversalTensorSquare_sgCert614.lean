-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sgCert614
-- name    : OAI.UniversalTensorSquare.sgCert614
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:18:09.302285+00:00
-- url     : https://prove2.me/theorems/95dbd273-9802-443d-8b45-a51ed5db2da5
-- title:
--   OAI.UniversalTensorSquare.sgCert614: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sgCert614` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sgCert614 : solveCompact 9 (.full [7,2]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
--       (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [7,2] (Equiv.refl (Fin 9)) sgB614 sgT614) sgFlag614 = -4
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.sgB614` and `OAI.UniversalTensorSquare.sgFlag614` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.sgT614` (definitions bundle `OAIQ259US003` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_110All`, `OAI.UniversalTensorSquare.degreeTree39_37All`, `OAI.UniversalTensorSquare.degreeTree62_727All`, `OAI.UniversalTensorSquare.degreeTree62_738All`, `OAI.UniversalTensorSquare.degreeTree62_958All`, `OAI.UniversalTensorSquare.sg19166`, `OAI.UniversalTensorSquare.sg21772`, `OAI.UniversalTensorSquare.sg21778`, `OAI.UniversalTensorSquare.sg21789`, `OAI.UniversalTensorSquare.sg22245`, `OAI.UniversalTensorSquare.sg22253`, `OAI.UniversalTensorSquare.sg23090`, `OAI.UniversalTensorSquare.sg23113`, `OAI.UniversalTensorSquare.sg37791`, `OAI.UniversalTensorSquare.sg37793`, `OAI.UniversalTensorSquare.sg42244`, `OAI.UniversalTensorSquare.sg42306`, `OAI.UniversalTensorSquare.sg42594`, `OAI.UniversalTensorSquare.sg42659`, `OAI.UniversalTensorSquare.sg9903`, `OAI.UniversalTensorSquare.sg9929` and `OAI.UniversalTensorSquare.sg9936` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean (declaration OAI.UniversalTensorSquare.sgCert614)

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

lemma sgCert614 : solveCompact 9 (.full [7,2]) (.full [4,2,1,1,1]) (.full [4,2,1,1,1])
    (certificateEdges [4,2,1,1,1] [4,2,1,1,1] [7,2] (Equiv.refl (Fin 9)) sgB614 sgT614) sgFlag614 = -4 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
