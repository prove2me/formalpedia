-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck14
-- name    : OAI.UniversalTensorSquare.degreeCheck14
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:07:54.023994+00:00
-- url     : https://prove2.me/theorems/8efb9a44-6421-47aa-8a07-c18ac7b64420
-- title:
--   OAI.UniversalTensorSquare.degreeCheck14: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.degreeCheck14` of [lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeChecks14.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeChecks14.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Balance Saxl.Columns`):
--
--   ```lean
--   lemma degreeCheck14 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
--       ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
--         semanticResidualCheck 14 4 2 (d+1) (e+1) (a+1) (c+1) degreeRows14_0 degreeP14
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.degreeRows14_0` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.degreeP14` (definitions bundle `OAIQ259US008` of this split); `OAI.UniversalTensorSquare.semanticResidualCheck` (definitions bundle `OAIQ259US012` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.degree_pos14` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeChecks14.lean (declaration OAI.UniversalTensorSquare.degreeCheck14)

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

lemma degreeCheck14 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      semanticResidualCheck 14 4 2 (d+1) (e+1) (a+1) (c+1) degreeRows14_0 degreeP14 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
