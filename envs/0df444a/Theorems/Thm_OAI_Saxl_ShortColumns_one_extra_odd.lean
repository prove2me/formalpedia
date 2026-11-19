-- Prove2me | Theorems.Thm_OAI_Saxl_ShortColumns_one_extra_odd
-- name    : OAI.Saxl.ShortColumns.one_extra_odd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T22:12:42.97446+00:00
-- url     : https://prove2.me/theorems/9f1ec8e5-179c-4dda-bb3c-9de23b7917ff
-- title:
--   OAI.Saxl.ShortColumns.one_extra_odd: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Saxl.ShortColumns.one_extra_odd` of [lean/OAI/RepresentationTheory/UniversalSquare/Band/OneExtra.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Band/OneExtra.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Saxl.ShortColumns`, with `open scoped TensorProduct`):
--
--   ```lean
--   theorem one_extra_odd (b : ℕ) (s : Tableau (2*b+1) (shape b 1))
--       (μ : YoungDiagram) (t : Tableau (2*b+1) μ)
--       (k : ℕ) (hk : Odd (μ.rowLen k)) (he : ∀ l, l ≠ k → Even (μ.rowLen l))
--       (hd : μ.colLen 0 ≤ 4) :
--       ∃ F : Representation.IntertwiningMap (spechtRep t)
--         (signTwist (rowColumnCyclic s).toRepresentation), F ≠ 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.ShortColumns.shape` (definitions bundle `OAIQ259US001` of this split); `OAI.Saxl.signTwist` (definitions bundle `OAIQ259US006` of this split); `OAI.Saxl.rowColumnCyclic` (definitions bundle `OAIQ259US021` of this split); `OAI.Saxl.Specht`, `OAI.Saxl.Tableau`, `OAI.Saxl.WordSpace`, `OAI.Saxl.spechtRep` and `OAI.Saxl.wordRep` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proofs of `OAI.Saxl.ShortColumns.one_extra_lifted` and `OAI.Saxl.ShortColumns.one_extra_transpose_lifted` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Band/OneExtra.lean (declaration OAI.Saxl.ShortColumns.one_extra_odd)

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021

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

theorem one_extra_odd (b : ℕ) (s : Tableau (2*b+1) (shape b 1))
    (μ : YoungDiagram) (t : Tableau (2*b+1) μ)
    (k : ℕ) (hk : Odd (μ.rowLen k)) (he : ∀ l, l ≠ k → Even (μ.rowLen l))
    (hd : μ.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (signTwist (rowColumnCyclic s).toRepresentation), F ≠ 0 := by
  sorry

end ShortColumns
end Saxl
end
end

end OAI
end
