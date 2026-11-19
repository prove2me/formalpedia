-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_even
-- name    : OAI.UniversalTensorSquare.rowSquare_even
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T17:19:09.917141+00:00
-- url     : https://prove2.me/theorems/38f350d1-d36e-4dd2-aa37-705ce1d9950d
-- title:
--   OAI.UniversalTensorSquare.rowSquare_even: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.rowSquare_even` of [lean/OAI/RepresentationTheory/UniversalSquare/Support/RowSquareTools.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/RowSquareTools.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open scoped TensorProduct`, `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma rowSquare_even {p rs : List ℕ} (m : ℕ)
--       (hp : GoodRows p) (hr : GoodRows rs) (hm : 0 < m)
--       (he : p = [m,m] ∨ transposeRows p = [m,m])
--       (hrl : rs.length ≤ 4) (hrs : rs.sum = 2*m) (heven : ∀ r ∈ rs, Even r) :
--       RowSquare p rs
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.GoodRows` and `OAI.UniversalTensorSquare.transposeRows` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.sg29998`, `OAI.UniversalTensorSquare.sg38391` and `OAI.UniversalTensorSquare.sg38981` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/RowSquareTools.lean (declaration OAI.UniversalTensorSquare.rowSquare_even)

import Mathlib
import Definitions.Def_OAIQ259US007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped TensorProduct
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma rowSquare_even {p rs : List ℕ} (m : ℕ)
    (hp : GoodRows p) (hr : GoodRows rs) (hm : 0 < m)
    (he : p = [m,m] ∨ transposeRows p = [m,m])
    (hrl : rs.length ≤ 4) (hrs : rs.sum = 2*m) (heven : ∀ r ∈ rs, Even r) :
    RowSquare p rs := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
