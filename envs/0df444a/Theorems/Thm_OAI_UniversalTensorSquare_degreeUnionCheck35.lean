-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionCheck35
-- name    : OAI.UniversalTensorSquare.degreeUnionCheck35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T14:01:36.179738+00:00
-- url     : https://prove2.me/theorems/f009bf86-e33f-4991-85b7-f1e8dc55a885
-- title:
--   OAI.UniversalTensorSquare.degreeUnionCheck35: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.degreeUnionCheck35` of [lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeRegions35.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeRegions35.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`):
--
--   ```lean
--   lemma degreeUnionCheck35 : ∀ h ≤ 15,
--       checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) h 35 34 degreeHalfRegions35 [] = true
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.checkRegionPrefixes` and `OAI.UniversalTensorSquare.degreeHalfRegions35` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.degreeQs35` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.degreeTree35` (definitions bundle `OAIQ259US008` of this split); `OAI.UniversalTensorSquare.quickResidual` (definitions bundle `OAIQ259US022` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.degreeCheck35` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeRegions35.lean (declaration OAI.UniversalTensorSquare.degreeUnionCheck35)

import Mathlib
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US022

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniversalTensorSquare

lemma degreeUnionCheck35 : ∀ h ≤ 15,
    checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) h 35 34 degreeHalfRegions35 [] = true := by
  sorry

end UniversalTensorSquare
end

end OAI
end
