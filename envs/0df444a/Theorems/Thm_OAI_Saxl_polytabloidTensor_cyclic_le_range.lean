-- Prove2me | Theorems.Thm_OAI_Saxl_polytabloidTensor_cyclic_le_range
-- name    : OAI.Saxl.polytabloidTensor_cyclic_le_range
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T17:06:09.775548+00:00
-- url     : https://prove2.me/theorems/a61a7b5f-cbdc-4e48-b7a3-51c82b4df270
-- title:
--   OAI.Saxl.polytabloidTensor_cyclic_le_range: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Saxl.polytabloidTensor_cyclic_le_range` of [lean/OAI/RepresentationTheory/UniversalSquare/Contraction/SquareDetection.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Contraction/SquareDetection.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Saxl`, with `open scoped TensorProduct`):
--
--   ```lean
--   lemma polytabloidTensor_cyclic_le_range {n : ℕ} {α β : YoungDiagram}
--       (a a' : Tableau n α) (b b' : Tableau n β) :
--       cyclic (wordRep n (α.colLen 0 * β.colLen 0))
--         (wordTensor _ _ _ (polytabloid a' ⊗ₜ[ℂ] polytabloid b')) ≤
--           (spechtTensorMap a b).range
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.spechtTensorMap` and `OAI.Saxl.wordTensor` (definitions bundle `OAIQ259US000` of this split); `OAI.Saxl.Specht`, `OAI.Saxl.Tableau`, `OAI.Saxl.WordSpace`, `OAI.Saxl.cyclic`, `OAI.Saxl.polytabloid`, `OAI.Saxl.spechtRep` and `OAI.Saxl.wordRep` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.rowSquare_even` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Contraction/SquareDetection.lean (declaration OAI.Saxl.polytabloidTensor_cyclic_le_range)

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma polytabloidTensor_cyclic_le_range {n : ℕ} {α β : YoungDiagram}
    (a a' : Tableau n α) (b b' : Tableau n β) :
    cyclic (wordRep n (α.colLen 0 * β.colLen 0))
      (wordTensor _ _ _ (polytabloid a' ⊗ₜ[ℂ] polytabloid b')) ≤
        (spechtTensorMap a b).range := by
  sorry

end Saxl
end
end

end OAI
end
