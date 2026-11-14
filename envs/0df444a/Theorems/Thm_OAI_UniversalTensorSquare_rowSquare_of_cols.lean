-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_of_cols
-- name    : OAI.UniversalTensorSquare.rowSquare_of_cols
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T13:06:52.405512+00:00
-- url     : https://prove2.me/theorems/cd9b1487-b4ed-4127-9c95-b643874ca98e
-- title:
--   OAI.UniversalTensorSquare.rowSquare_of_cols: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.rowSquare_of_cols` of [lean/OAI/RepresentationTheory/UniversalSquare/Support/RowSquareTools.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/RowSquareTools.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open scoped TensorProduct`, `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma rowSquare_of_cols {p q cs : List ℕ} (hp : GoodRows p) (hq : GoodRows q)
--       (he : cs = transposeRows p ∨ cs = p)
--       (h : SquareOccurs (columnShape cs) (columnShape (transposeRows q))) : RowSquare p q
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.GoodRows`, `OAI.UniversalTensorSquare.transposeRows` and `OAI.Saxl.Columns.columnShape` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.RowSquare` and `OAI.UniversalTensorSquare.SquareOccurs` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree24_16All`, `OAI.UniversalTensorSquare.rowSquare_short`, `OAI.UniversalTensorSquare.sg11963`, `OAI.UniversalTensorSquare.sg11976`, `OAI.UniversalTensorSquare.sg11984`, `OAI.UniversalTensorSquare.sg11986`, `OAI.UniversalTensorSquare.sg12002`, `OAI.UniversalTensorSquare.sg12004`, `OAI.UniversalTensorSquare.sg12005`, `OAI.UniversalTensorSquare.sg12018`, `OAI.UniversalTensorSquare.sg12097`, `OAI.UniversalTensorSquare.sg12149`, `OAI.UniversalTensorSquare.sg12156`, `OAI.UniversalTensorSquare.sg12210`, `OAI.UniversalTensorSquare.sg12211`, `OAI.UniversalTensorSquare.sg12219`, `OAI.UniversalTensorSquare.sg12224`, `OAI.UniversalTensorSquare.sg12225`, `OAI.UniversalTensorSquare.sg21946` and `OAI.UniversalTensorSquare.sg21998` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/RowSquareTools.lean (declaration OAI.UniversalTensorSquare.rowSquare_of_cols)

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

lemma rowSquare_of_cols {p q cs : List ℕ} (hp : GoodRows p) (hq : GoodRows q)
    (he : cs = transposeRows p ∨ cs = p)
    (h : SquareOccurs (columnShape cs) (columnShape (transposeRows q))) : RowSquare p q := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
