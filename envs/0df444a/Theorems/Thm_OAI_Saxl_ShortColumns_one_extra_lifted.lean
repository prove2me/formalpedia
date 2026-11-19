-- Prove2me | Theorems.Thm_OAI_Saxl_ShortColumns_one_extra_lifted
-- name    : OAI.Saxl.ShortColumns.one_extra_lifted
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T22:12:33.833099+00:00
-- url     : https://prove2.me/theorems/6d2e9fa3-9f2a-4ad1-a2c6-816b80d84816
-- title:
--   OAI.Saxl.ShortColumns.one_extra_lifted: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Saxl.ShortColumns.one_extra_lifted` of [lean/OAI/RepresentationTheory/UniversalSquare/Band/TwoExtras.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Band/TwoExtras.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Saxl.ShortColumns`, with `open scoped TensorProduct`):
--
--   ```lean
--   lemma one_extra_lifted (r d : ℕ) (s : Tableau r (shape (r/2) (r%2)))
--       (φ : Fin ((shape (r/2) (r%2)).transpose.colLen 0 *
--         (shape (r/2) (r%2)).colLen 0) → Fin d) (hφ : Function.Injective φ)
--       (μ : YoungDiagram) (t : Tableau r μ) (hp : RowParity (r%2) μ)
--       (hd : μ.colLen 0 ≤ 4) :
--       ∃ F : Representation.IntertwiningMap (spechtRep t)
--         (signTwist (cyclic (wordRep r d) (letterLift φ (rowColumnWord s))).toRepresentation),
--         Function.Injective F
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.letterLift` (definitions bundle `OAIQ259US000` of this split); `OAI.Saxl.ShortColumns.RowParity` and `OAI.Saxl.ShortColumns.shape` (definitions bundle `OAIQ259US001` of this split); `OAI.Saxl.signTwist` (definitions bundle `OAIQ259US006` of this split); `OAI.Saxl.rowColumnWord` (definitions bundle `OAIQ259US021` of this split); `OAI.Saxl.Specht`, `OAI.Saxl.Tableau`, `OAI.Saxl.WordSpace`, `OAI.Saxl.cyclic`, `OAI.Saxl.spechtRep` and `OAI.Saxl.wordRep` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.candidateExtrasWord_contraction` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Band/TwoExtras.lean (declaration OAI.Saxl.ShortColumns.one_extra_lifted)

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

lemma one_extra_lifted (r d : ℕ) (s : Tableau r (shape (r/2) (r%2)))
    (φ : Fin ((shape (r/2) (r%2)).transpose.colLen 0 *
      (shape (r/2) (r%2)).colLen 0) → Fin d) (hφ : Function.Injective φ)
    (μ : YoungDiagram) (t : Tableau r μ) (hp : RowParity (r%2) μ)
    (hd : μ.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (signTwist (cyclic (wordRep r d) (letterLift φ (rowColumnWord s))).toRepresentation),
      Function.Injective F := by
  sorry

end ShortColumns
end Saxl
end
end

end OAI
end
