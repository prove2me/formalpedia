-- Prove2me | Theorems.Thm_OAI_Saxl_ShortColumns_even_columnSquare_support
-- name    : OAI.Saxl.ShortColumns.even_columnSquare_support
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T17:06:26.049196+00:00
-- url     : https://prove2.me/theorems/d1a91911-1997-4149-8232-79adc1c01bce
-- title:
--   OAI.Saxl.ShortColumns.even_columnSquare_support: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Saxl.ShortColumns.even_columnSquare_support` of [lean/OAI/RepresentationTheory/UniversalSquare/Band/OneExtra.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Band/OneExtra.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Saxl.ShortColumns`, with `open scoped TensorProduct`):
--
--   ```lean
--   theorem even_columnSquare_support (b : ℕ) (μ : YoungDiagram) (t : Tableau (2*b) μ)
--       (he : ∀ i, Even (μ.rowLen i)) (hd : μ.colLen 0 ≤ 4) :
--       ∃ F : Representation.IntertwiningMap (spechtRep t)
--         (columnSquareCyclic (evenTableau b)).toRepresentation, F ≠ 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.ShortColumns.shape` (definitions bundle `OAIQ259US001` of this split); `OAI.Saxl.columnSquareCyclic` and `OAI.Saxl.ShortColumns.evenTableau` (definitions bundle `OAIQ259US006` of this split); `OAI.Saxl.Specht`, `OAI.Saxl.Tableau`, `OAI.Saxl.WordSpace`, `OAI.Saxl.spechtRep` and `OAI.Saxl.wordRep` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proofs of `OAI.Saxl.ShortColumns.one_extra_lifted`, `OAI.Saxl.ShortColumns.one_extra_transpose_lifted` and `OAI.UniversalTensorSquare.rowSquare_even` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Band/OneExtra.lean (declaration OAI.Saxl.ShortColumns.even_columnSquare_support)

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006

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

namespace ShortColumns

theorem even_columnSquare_support (b : ℕ) (μ : YoungDiagram) (t : Tableau (2*b) μ)
    (he : ∀ i, Even (μ.rowLen i)) (hd : μ.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (columnSquareCyclic (evenTableau b)).toRepresentation, F ≠ 0 := by
  sorry

end ShortColumns
end Saxl
end
end

end OAI
end
