-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck151_4_3
-- name    : OAI.UniversalTensorSquare.degreeCheck151_4_3
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T18:29:31.936047+00:00
-- url     : https://prove2.me/theorems/5c8057bb-3434-4480-be5d-e9934e3996db
-- title:
--   OAI.UniversalTensorSquare.degreeCheck151_4_3: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.degreeCheck151_4_3` of [lean/OAI/RepresentationTheory/UniversalSquare/Finite/NumericalDegree151.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/NumericalDegree151.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Balance Saxl.Columns`):
--
--   ```lean
--   lemma degreeCheck151_4_3 :
--       ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
--         residualCheck 151 14 23 5 4 (a+1) (c+1) degreeRows151_0 degreeP151
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.degreeRows151_0` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.degreeP151` (definitions bundle `OAIQ259US008` of this split); `OAI.UniversalTensorSquare.residualCheck` (definitions bundle `OAIQ259US012` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.degreeCheck151` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/NumericalDegree151.lean (declaration OAI.UniversalTensorSquare.degreeCheck151_4_3)

import Mathlib
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US012

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck151_4_3 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 5 4 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
