-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_24
-- name    : OAI.UniversalTensorSquare.smallCert13_24
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-16T02:48:41.616375+00:00
-- url     : https://prove2.me/theorems/6c96bcea-3d53-430e-9e23-75f9f1d11c67
-- title:
--   OAI.UniversalTensorSquare.smallCert13_24: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.smallCert13_24` of [lean/OAI/RepresentationTheory/UniversalSquare/Finite/SmallContracts13_6.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/SmallContracts13_6.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma smallCert13_24 : solveChoices smallChoices13_24 (.full [4,2,2,2,2,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
--       (certificateEdges [4,4,3,2] [4,4,3,2] [4,2,2,2,2,1] (Equiv.refl (Fin 13)) smallB13_24 smallT13_24) smallFlag13_24 = -54
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.smallB13_24` (definitions bundle `OAIQ259US003` of this split); `OAI.UniversalTensorSquare.smallFlag13_24` and `OAI.UniversalTensorSquare.smallT13_24` (definitions bundle `OAIQ259US004` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveChoices` (definitions bundle `OAIQ259US006` of this split); `OAI.UniversalTensorSquare.smallChoices13_24` (definitions bundle `OAIQ259US016` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.smallSupport13_24` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/SmallContracts13_6.lean (declaration OAI.UniversalTensorSquare.smallCert13_24)

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US016

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

lemma smallCert13_24 : solveChoices smallChoices13_24 (.full [4,2,2,2,2,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,2,2,2,2,1] (Equiv.refl (Fin 13)) smallB13_24 smallT13_24) smallFlag13_24 = -54 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
