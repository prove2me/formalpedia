-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_eightCertificate0
-- name    : OAI.UniversalTensorSquare.eightCertificate0
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-15T21:45:45.089405+00:00
-- url     : https://prove2.me/theorems/52d42559-0875-489e-ab8c-f2ff6562e191
-- title:
--   OAI.UniversalTensorSquare.eightCertificate0: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.eightCertificate0` of [lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeEight.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeEight.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns`):
--
--   ```lean
--   lemma eightCertificate0 : contractionInteger [4,2,1,1] [4,2,1,1] [1,1,1,1,1,1,1,1]
--       (Equiv.refl (Fin 8)) eightPlaceB0 eightPlaceT0 eightFlag0 = 6
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.eightFlag0`, `OAI.UniversalTensorSquare.eightPlaceB0` and `OAI.UniversalTensorSquare.eightPlaceT0` (definitions bundle `OAIQ259US002` of this split); `OAI.Saxl.Columns.contractionInteger` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_123All`, `OAI.UniversalTensorSquare.degreeTree39_13All`, `OAI.UniversalTensorSquare.degreeTree39_14All`, `OAI.UniversalTensorSquare.degreeTree39_77All`, `OAI.UniversalTensorSquare.degreeTree41_9All` and `OAI.UniversalTensorSquare.degreeTree43_112All` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeEight.lean (declaration OAI.UniversalTensorSquare.eightCertificate0)

import Mathlib
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Saxl Saxl.Columns
namespace UniversalTensorSquare

lemma eightCertificate0 : contractionInteger [4,2,1,1] [4,2,1,1] [1,1,1,1,1,1,1,1]
    (Equiv.refl (Fin 8)) eightPlaceB0 eightPlaceT0 eightFlag0 = 6 := by
  sorry

end UniversalTensorSquare
end

end OAI
end
