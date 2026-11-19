-- Prove2me | Theorems.Thm_OAI_Saxl_even_rows_symmetricPairs_support
-- name    : OAI.Saxl.even_rows_symmetricPairs_support
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T17:06:09.633704+00:00
-- url     : https://prove2.me/theorems/0912660f-c019-4536-9e31-8f991e46f2b5
-- title:
--   OAI.Saxl.even_rows_symmetricPairs_support: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Saxl.even_rows_symmetricPairs_support` of [lean/OAI/RepresentationTheory/UniversalSquare/Contraction/SymmetricPairs.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Contraction/SymmetricPairs.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Saxl`, with `open scoped TensorProduct`):
--
--   ```lean
--   theorem even_rows_symmetricPairs_support {n m d : ℕ}
--       (e : Fin n ≃ Fin m ⊕ Fin m) (μ : YoungDiagram) (t : Tableau n μ)
--       (he : ∀ i, Even (μ.rowLen i)) (hd : μ.colLen 0 ≤ d) :
--       ∃ F : Representation.IntertwiningMap (spechtRep t)
--         (cyclic (wordRep n d) (symmetricPairs e d)).toRepresentation, F ≠ 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.symmetricPairs` (definitions bundle `OAIQ259US006` of this split); `OAI.Saxl.Specht`, `OAI.Saxl.Tableau`, `OAI.Saxl.WordSpace`, `OAI.Saxl.cyclic`, `OAI.Saxl.spechtRep` and `OAI.Saxl.wordRep` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proofs of `OAI.Saxl.ShortColumns.one_extra_lifted`, `OAI.Saxl.ShortColumns.one_extra_transpose_lifted` and `OAI.Saxl.even_rows_shortPair_support` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Contraction/SymmetricPairs.lean (declaration OAI.Saxl.even_rows_symmetricPairs_support)

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

theorem even_rows_symmetricPairs_support {n m d : ℕ}
    (e : Fin n ≃ Fin m ⊕ Fin m) (μ : YoungDiagram) (t : Tableau n μ)
    (he : ∀ i, Even (μ.rowLen i)) (hd : μ.colLen 0 ≤ d) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) (symmetricPairs e d)).toRepresentation, F ≠ 0 := by
  sorry

end Saxl
end
end

end OAI
end
