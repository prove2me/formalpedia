-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_transposeRows_eq
-- name    : OAI.UniversalTensorSquare.transposeRows_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:33:16.878735+00:00
-- url     : https://prove2.me/theorems/da5581d3-38c2-4747-b8a5-0dd8ef87b45c
-- title:
--   OAI.UniversalTensorSquare.transposeRows_eq: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.transposeRows_eq` of [lean/OAI/RepresentationTheory/UniversalSquare/Support/NumericalSupport.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/NumericalSupport.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Balance Saxl.Columns`):
--
--   ```lean
--   lemma transposeRows_eq {rs : List ℕ} (h : GoodRows rs) :
--       transposeRows rs = (rowDiagram rs).transpose.rowLens
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.GoodRows`, `OAI.UniversalTensorSquare.rowDiagram` and `OAI.UniversalTensorSquare.transposeRows` (definitions bundle `OAIQ259US001` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.rowSquare_short` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/NumericalSupport.lean (declaration OAI.UniversalTensorSquare.transposeRows_eq)

import Mathlib
import Definitions.Def_OAIQ259US001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma transposeRows_eq {rs : List ℕ} (h : GoodRows rs) :
    transposeRows rs = (rowDiagram rs).transpose.rowLens := by
  sorry

end UniversalTensorSquare

end
end

end OAI
end
