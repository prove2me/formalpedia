-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionBranch62_1240
-- name    : OAI.UniversalTensorSquare.degreeUnionBranch62_1240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T06:44:07.304879+00:00
-- url     : https://prove2.me/theorems/2467b492-8b54-40a2-a705-9dae9d7bcfe1
-- title:
--   OAI.UniversalTensorSquare.degreeUnionBranch62_1240: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.degreeUnionBranch62_1240` of [lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeLeaves62.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeLeaves62.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`):
--
--   ```lean
--   lemma degreeUnionBranch62_1240 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 42 6 degreeUnionState62_1240 [6,14] = true
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.checkRegionPrefixes` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.degreeQs62` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.degreeTree62` and `OAI.UniversalTensorSquare.degreeUnionState62_1240` (definitions bundle `OAIQ259US021` of this split); `OAI.UniversalTensorSquare.quickResidual` (definitions bundle `OAIQ259US022` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.degreeUnionBranch62_1237` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeLeaves62.lean (declaration OAI.UniversalTensorSquare.degreeUnionBranch62_1240)

import Mathlib
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_1240 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 42 6 degreeUnionState62_1240 [6,14] = true := by
  sorry

end UniversalTensorSquare
end

end OAI
end
