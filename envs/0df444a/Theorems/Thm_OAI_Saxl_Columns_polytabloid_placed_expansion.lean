-- Prove2me | Theorems.Thm_OAI_Saxl_Columns_polytabloid_placed_expansion
-- name    : OAI.Saxl.Columns.polytabloid_placed_expansion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-16T02:38:49.443087+00:00
-- url     : https://prove2.me/theorems/de171cf8-9c04-48cc-b84d-d705f8a9d59a
-- title:
--   OAI.Saxl.Columns.polytabloid_placed_expansion: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Saxl.Columns.polytabloid_placed_expansion` of [lean/OAI/RepresentationTheory/UniversalSquare/Contraction/ColumnCertificates.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Contraction/ColumnCertificates.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Saxl.Columns`, with `open scoped TensorProduct`):
--
--   ```lean
--   lemma polytabloid_placed_expansion {n : ℕ} (μ : YoungDiagram)
--       (e : Fin n ≃ Fin μ.transpose.rowLens.sum) :
--       polytabloid (e.trans (columnTableau μ)) =
--         ∑ π : Perms μ.transpose.rowLens, sg π • Pi.single (signedRowWord μ π ∘ e) 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.columnTableau` (definitions bundle `OAIQ259US000` of this split); `OAI.Saxl.Columns.Perms`, `OAI.Saxl.Columns.permsFintype`, `OAI.Saxl.Columns.sg` and `OAI.Saxl.Columns.signedRowWord` (definitions bundle `OAIQ259US006` of this split); `OAI.Saxl.WordSpace` and `OAI.Saxl.polytabloid` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.eight_positive10` and `OAI.UniversalTensorSquare.eight_positive7` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Contraction/ColumnCertificates.lean (declaration OAI.Saxl.Columns.polytabloid_placed_expansion)

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

namespace Columns

lemma polytabloid_placed_expansion {n : ℕ} (μ : YoungDiagram)
    (e : Fin n ≃ Fin μ.transpose.rowLens.sum) :
    polytabloid (e.trans (columnTableau μ)) =
      ∑ π : Perms μ.transpose.rowLens, sg π • Pi.single (signedRowWord μ π ∘ e) 1 := by
  sorry

end Columns
end Saxl
end
end

end OAI
end
