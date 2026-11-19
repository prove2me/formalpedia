-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg564
-- name    : OAI.UniversalTensorSquare.sg564
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T22:44:28.234849+00:00
-- url     : https://prove2.me/theorems/21916a98-5f44-438c-837f-7d102c6f36b1
-- title:
--   OAI.UniversalTensorSquare.sg564: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg564` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg564 : RowSquare [4,3,1,1] [2,2,2,2,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_116All`, `OAI.UniversalTensorSquare.degreeTree62_209All`, `OAI.UniversalTensorSquare.sg16783`, `OAI.UniversalTensorSquare.sg27245`, `OAI.UniversalTensorSquare.sg28053`, `OAI.UniversalTensorSquare.sg32969`, `OAI.UniversalTensorSquare.sg34402`, `OAI.UniversalTensorSquare.sg34545`, `OAI.UniversalTensorSquare.sg34571`, `OAI.UniversalTensorSquare.sg34595`, `OAI.UniversalTensorSquare.sg35323`, `OAI.UniversalTensorSquare.sg35325`, `OAI.UniversalTensorSquare.sg35326`, `OAI.UniversalTensorSquare.sg35328`, `OAI.UniversalTensorSquare.sg35330`, `OAI.UniversalTensorSquare.sg35332`, `OAI.UniversalTensorSquare.sg35439`, `OAI.UniversalTensorSquare.sg36980`, `OAI.UniversalTensorSquare.sg37629`, `OAI.UniversalTensorSquare.sg37633`, `OAI.UniversalTensorSquare.sg37636`, `OAI.UniversalTensorSquare.sg38322`, `OAI.UniversalTensorSquare.sg38323`, `OAI.UniversalTensorSquare.sg38875`, `OAI.UniversalTensorSquare.sg39433`, `OAI.UniversalTensorSquare.sg39447` and `OAI.UniversalTensorSquare.sg40732` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean (declaration OAI.UniversalTensorSquare.sg564)

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
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg564 : RowSquare [4,3,1,1] [2,2,2,2,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
