-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_4
-- name    : OAI.UniversalTensorSquare.smallCert13_4
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T23:06:27.283208+00:00
-- url     : https://prove2.me/theorems/49987b01-e00d-445c-bb2e-812671fc0d1a
-- title:
--   OAI.UniversalTensorSquare.smallCert13_4: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.smallCert13_4` of [lean/OAI/RepresentationTheory/UniversalSquare/Finite/SmallContracts13_1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/SmallContracts13_1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma smallCert13_4 : solveCompact 13 (.full [5,4,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
--       (certificateEdges [4,4,3,2] [4,4,3,2] [5,4,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_4 smallT13_4) smallFlag13_4 = -13
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.smallB13_4`, `OAI.UniversalTensorSquare.smallFlag13_4` and `OAI.UniversalTensorSquare.smallT13_4` (definitions bundle `OAIQ259US004` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.smallSupport13_4` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/SmallContracts13_1.lean (declaration OAI.UniversalTensorSquare.smallCert13_4)

import Mathlib
import Definitions.Def_OAIQ259US004
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

lemma smallCert13_4 : solveCompact 13 (.full [5,4,1,1,1,1]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [5,4,1,1,1,1] (Equiv.refl (Fin 13)) smallB13_4 smallT13_4) smallFlag13_4 = -13 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
