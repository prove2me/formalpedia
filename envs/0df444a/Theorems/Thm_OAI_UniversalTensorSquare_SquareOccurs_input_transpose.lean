-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_SquareOccurs_input_transpose
-- name    : OAI.UniversalTensorSquare.SquareOccurs.input_transpose
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T17:06:22.24819+00:00
-- url     : https://prove2.me/theorems/b836fc5f-f1b8-4799-9e81-2f83403ca370
-- title:
--   OAI.UniversalTensorSquare.SquareOccurs.input_transpose: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.SquareOccurs.input_transpose` of [lean/OAI/RepresentationTheory/UniversalSquare/Support/SquareSemigroup.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/SquareSemigroup.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open scoped TensorProduct`, `open Saxl Columns`):
--
--   ```lean
--   lemma SquareOccurs.input_transpose {α μ : YoungDiagram} (h : SquareOccurs α μ) :
--       SquareOccurs α.transpose μ
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.SquareOccurs` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.rowSquare_even` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/SquareSemigroup.lean (declaration OAI.UniversalTensorSquare.SquareOccurs.input_transpose)

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
open Saxl Columns

lemma SquareOccurs.input_transpose {α μ : YoungDiagram} (h : SquareOccurs α μ) :
    SquareOccurs α.transpose μ := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
