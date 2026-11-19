-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_area_le_refined
-- name    : OAI.UniversalTensorSquare.area_le_refined
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T17:06:19.705474+00:00
-- url     : https://prove2.me/theorems/58880cec-095e-4ed7-9cce-e5ed9a19a311
-- title:
--   OAI.UniversalTensorSquare.area_le_refined: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.area_le_refined` of [lean/OAI/RepresentationTheory/UniversalSquare/Capacity/RefinedCapacity.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Capacity/RefinedCapacity.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl`):
--
--   ```lean
--   lemma area_le_refined (μ : YoungDiagram) {i j U V X Y H W : ℕ}
--       (hi : 0 < i) (hj : 0 < j) (hU : colPrefix μ i ≤ U) (hV : rowPrefix μ j ≤ V)
--       (hX : μ.colLen (i-1) ≤ X) (hY : μ.rowLen (j-1) ≤ Y)
--       (hH : H ≤ μ.colLen 0) (hW : W ≤ μ.rowLen 0) (hHp : 0 < H) (hWp : 0 < W) :
--       μ.card ≤ refinedArea i j U V X Y H W
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.rowPrefix` and `OAI.UniversalTensorSquare.colPrefix` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.refinedArea` (definitions bundle `OAIQ259US002` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.refined_capacity_dichotomy` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Capacity/RefinedCapacity.lean (declaration OAI.UniversalTensorSquare.area_le_refined)

import Mathlib
import Definitions.Def_OAIQ259US001
import Definitions.Def_OAIQ259US002

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

lemma area_le_refined (μ : YoungDiagram) {i j U V X Y H W : ℕ}
    (hi : 0 < i) (hj : 0 < j) (hU : colPrefix μ i ≤ U) (hV : rowPrefix μ j ≤ V)
    (hX : μ.colLen (i-1) ≤ X) (hY : μ.rowLen (j-1) ≤ Y)
    (hH : H ≤ μ.colLen 0) (hW : W ≤ μ.rowLen 0) (hHp : 0 < H) (hWp : 0 < W) :
    μ.card ≤ refinedArea i j U V X Y H W := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
