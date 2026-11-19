-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_42
-- name    : OAI.UniversalTensorSquare.smallCert13_42
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T17:47:14.139747+00:00
-- url     : https://prove2.me/theorems/c0d283ac-e616-4676-b791-cefbb3d6e323
-- title:
--   OAI.UniversalTensorSquare.smallCert13_42: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.smallCert13_42` of [lean/OAI/RepresentationTheory/UniversalSquare/Finite/SmallContracts13_10.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/SmallContracts13_10.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma smallCert13_42 : solveChoices smallChoices13_42 (.full [4,4,3,2]) (.full [4,4,3,2]) (.full [4,4,3,2])
--       (certificateEdges [4,4,3,2] [4,4,3,2] [4,4,3,2] (Equiv.refl (Fin 13)) smallB13_42 smallT13_42) smallFlag13_42 = 4
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.smallB13_42` (definitions bundle `OAIQ259US003` of this split); `OAI.UniversalTensorSquare.smallFlag13_42` and `OAI.UniversalTensorSquare.smallT13_42` (definitions bundle `OAIQ259US004` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveChoices` (definitions bundle `OAIQ259US006` of this split); `OAI.UniversalTensorSquare.smallChoices13_42` (definitions bundle `OAIQ259US017` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.smallSupport13_42` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/SmallContracts13_10.lean (declaration OAI.UniversalTensorSquare.smallCert13_42)

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US017

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

lemma smallCert13_42 : solveChoices smallChoices13_42 (.full [4,4,3,2]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [4,4,3,2] (Equiv.refl (Fin 13)) smallB13_42 smallT13_42) smallFlag13_42 = 4 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
