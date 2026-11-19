-- Prove2me | Theorems.Thm_OAI_Saxl_one_odd_row_symmetricPartialPairs_support
-- name    : OAI.Saxl.one_odd_row_symmetricPartialPairs_support
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T17:06:25.310213+00:00
-- url     : https://prove2.me/theorems/37b64cac-7028-47df-a978-72a206e968b0
-- title:
--   OAI.Saxl.one_odd_row_symmetricPartialPairs_support: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Saxl.one_odd_row_symmetricPartialPairs_support` of [lean/OAI/RepresentationTheory/UniversalSquare/Support/SingletonPairs.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/SingletonPairs.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Saxl`):
--
--   ```lean
--   theorem one_odd_row_symmetricPartialPairs_support {n m d : ℕ}
--       (e : Fin n ≃ Fin (m+1) ⊕ Fin m) (i : Fin m ↪ Fin (m+1))
--       (v : Fin d → ℂ) (hv : v ≠ 0)
--       (μ : YoungDiagram) (t : Tableau n μ)
--       (k : ℕ) (hk : Odd (μ.rowLen k)) (he : ∀ l, l ≠ k → Even (μ.rowLen l))
--       (hd : μ.colLen 0 ≤ d) :
--       ∃ F : Representation.IntertwiningMap (spechtRep t)
--         (cyclic (wordRep n d) (symmetricPartialPairs e i v)).toRepresentation, F ≠ 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.symmetricPartialPairs` (definitions bundle `OAIQ259US007` of this split); `OAI.Saxl.Specht`, `OAI.Saxl.Tableau`, `OAI.Saxl.WordSpace`, `OAI.Saxl.cyclic`, `OAI.Saxl.spechtRep` and `OAI.Saxl.wordRep` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proof of `OAI.Saxl.ShortColumns.one_extra_odd` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/SingletonPairs.lean (declaration OAI.Saxl.one_odd_row_symmetricPartialPairs_support)

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace Saxl

theorem one_odd_row_symmetricPartialPairs_support {n m d : ℕ}
    (e : Fin n ≃ Fin (m+1) ⊕ Fin m) (i : Fin m ↪ Fin (m+1))
    (v : Fin d → ℂ) (hv : v ≠ 0)
    (μ : YoungDiagram) (t : Tableau n μ)
    (k : ℕ) (hk : Odd (μ.rowLen k)) (he : ∀ l, l ≠ k → Even (μ.rowLen l))
    (hd : μ.colLen 0 ≤ d) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) (symmetricPartialPairs e i v)).toRepresentation, F ≠ 0 := by
  sorry

end Saxl
end
end

end OAI
end
