-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck37
-- name    : OAI.UniversalTensorSquare.degreeCheck37
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T18:27:07.826701+00:00
-- url     : https://prove2.me/theorems/669c8702-e07e-4763-af4f-34f086dd3590
-- title:
--   OAI.UniversalTensorSquare.degreeCheck37: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.degreeCheck37` of [lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeChecks37.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeChecks37.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Balance Saxl.Columns`):
--
--   ```lean
--   lemma degreeCheck37 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
--       ∀ a ∈ List.range degreeRows37_0.length, ∀ c ∈ List.range degreeRows37_0.length,
--         semanticResidualCheck 37 6 8 (d+1) (e+1) (a+1) (c+1) degreeRows37_0 degreeP37
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.degreeRows37_0` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.degreeP37` (definitions bundle `OAIQ259US008` of this split); `OAI.UniversalTensorSquare.semanticResidualCheck` (definitions bundle `OAIQ259US012` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.degree_pos37` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeChecks37.lean (declaration OAI.UniversalTensorSquare.degreeCheck37)

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

lemma degreeCheck37 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows37_0.length, ∀ c ∈ List.range degreeRows37_0.length,
      semanticResidualCheck 37 6 8 (d+1) (e+1) (a+1) (c+1) degreeRows37_0 degreeP37 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
