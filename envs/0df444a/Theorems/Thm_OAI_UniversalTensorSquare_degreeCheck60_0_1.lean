-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_degreeCheck60_0_1
-- name    : OAI.UniversalTensorSquare.degreeCheck60_0_1
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T13:35:03.268203+00:00
-- url     : https://prove2.me/theorems/ef55ca81-edb6-4519-9427-ddbd127935e2
-- title:
--   OAI.UniversalTensorSquare.degreeCheck60_0_1: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.degreeCheck60_0_1` of [lean/OAI/RepresentationTheory/UniversalSquare/Finite/NumericalDegree60.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/NumericalDegree60.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Balance Saxl.Columns`):
--
--   ```lean
--   lemma degreeCheck60_0_1 :
--       ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
--         residualCheck 60 8 12 1 2 (a+1) (c+1) degreeRows60_0 degreeP60
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.degreeRows60_0` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.degreeP60` (definitions bundle `OAIQ259US010` of this split); `OAI.UniversalTensorSquare.residualCheck` (definitions bundle `OAIQ259US012` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.degreeCheck60` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/NumericalDegree60.lean (declaration OAI.UniversalTensorSquare.degreeCheck60_0_1)

import Mathlib
import Definitions.Def_OAIQ259US010
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

lemma degreeCheck60_0_1 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 1 2 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
