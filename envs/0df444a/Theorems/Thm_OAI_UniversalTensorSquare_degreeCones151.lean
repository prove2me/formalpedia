-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_degreeCones151
-- name    : OAI.UniversalTensorSquare.degreeCones151
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T18:28:48.578758+00:00
-- url     : https://prove2.me/theorems/c718009f-fc24-46b1-86d8-c2fbcde69240
-- title:
--   OAI.UniversalTensorSquare.degreeCones151: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.degreeCones151` of [lean/OAI/RepresentationTheory/UniversalSquare/Finite/NumericalDegree151.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/NumericalDegree151.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Balance Saxl.Columns`):
--
--   ```lean
--   lemma degreeCones151 : ∀ q ∈ degreeQs151, ∀ μ : YoungDiagram, μ.card = 151 →
--       RowsDom μ.rowLens q → SquareOccurs (candidate 14 11 1) μ
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowsDom` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.degreeQs151` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.SquareOccurs` and `OAI.UniversalTensorSquare.candidate` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.degree_pos151` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/NumericalDegree151.lean (declaration OAI.UniversalTensorSquare.degreeCones151)

import Mathlib
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US007

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

lemma degreeCones151 : ∀ q ∈ degreeQs151, ∀ μ : YoungDiagram, μ.card = 151 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 14 11 1) μ := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
