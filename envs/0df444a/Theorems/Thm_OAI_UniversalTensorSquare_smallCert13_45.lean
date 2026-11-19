-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_smallCert13_45
-- name    : OAI.UniversalTensorSquare.smallCert13_45
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T17:47:14.031719+00:00
-- url     : https://prove2.me/theorems/d0f2748b-63ed-4281-b327-60fa86384f2a
-- title:
--   OAI.UniversalTensorSquare.smallCert13_45: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.smallCert13_45` of [lean/OAI/RepresentationTheory/UniversalSquare/Finite/SmallContracts13_11.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/SmallContracts13_11.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma smallCert13_45 : solveChoices smallChoices13_45 (.full [3,3,3,2,2]) (.full [4,4,3,2]) (.full [4,4,3,2])
--       (certificateEdges [4,4,3,2] [4,4,3,2] [3,3,3,2,2] (Equiv.refl (Fin 13)) smallB13_45 smallT13_45) smallFlag13_45 = -4
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.smallB13_45` (definitions bundle `OAIQ259US003` of this split); `OAI.UniversalTensorSquare.smallFlag13_45` and `OAI.UniversalTensorSquare.smallT13_45` (definitions bundle `OAIQ259US004` of this split); `OAI.Saxl.Columns.certificateEdges` and `OAI.Saxl.Columns.solveChoices` (definitions bundle `OAIQ259US006` of this split); `OAI.UniversalTensorSquare.smallChoices13_45` (definitions bundle `OAIQ259US019` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.smallSupport13_45` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/SmallContracts13_11.lean (declaration OAI.UniversalTensorSquare.smallCert13_45)

import Mathlib
import Definitions.Def_OAIQ259US003
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US019

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

lemma smallCert13_45 : solveChoices smallChoices13_45 (.full [3,3,3,2,2]) (.full [4,4,3,2]) (.full [4,4,3,2])
    (certificateEdges [4,4,3,2] [4,4,3,2] [3,3,3,2,2] (Equiv.refl (Fin 13)) smallB13_45 smallT13_45) smallFlag13_45 = -4 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
