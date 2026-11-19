-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_strip_area_identity
-- name    : OAI.UniversalTensorSquare.strip_area_identity
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T17:06:14.729891+00:00
-- url     : https://prove2.me/theorems/0ed3aba8-b81b-472a-b31d-35c1af515a5f
-- title:
--   OAI.UniversalTensorSquare.strip_area_identity: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.strip_area_identity` of [lean/OAI/RepresentationTheory/UniversalSquare/Capacity/Capacity.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Capacity/Capacity.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl`):
--
--   ```lean
--   lemma strip_area_identity (μ : YoungDiagram) (i j : ℕ) :
--       μ.card + ((rowTruncate μ j).cells ∩ (colTruncate μ i).cells).card =
--         rowPrefix μ j + colPrefix μ i +
--           (μ.cells \ ((rowTruncate μ j).cells ∪ (colTruncate μ i).cells)).card
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.colTruncate`, `OAI.Saxl.rowPrefix`, `OAI.Saxl.rowTruncate` and `OAI.UniversalTensorSquare.colPrefix` (definitions bundle `OAIQ259US001` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.area_le_refined` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Capacity/Capacity.lean (declaration OAI.UniversalTensorSquare.strip_area_identity)

import Mathlib
import Definitions.Def_OAIQ259US001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl

lemma strip_area_identity (μ : YoungDiagram) (i j : ℕ) :
    μ.card + ((rowTruncate μ j).cells ∩ (colTruncate μ i).cells).card =
      rowPrefix μ j + colPrefix μ i +
        (μ.cells \ ((rowTruncate μ j).cells ∪ (colTruncate μ i).cells)).card := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
