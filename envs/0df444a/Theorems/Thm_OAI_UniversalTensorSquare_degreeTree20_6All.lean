-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_degreeTree20_6All
-- name    : OAI.UniversalTensorSquare.degreeTree20_6All
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T18:29:05.001196+00:00
-- url     : https://prove2.me/theorems/039c88b5-7568-4d0e-9458-f5952613f9d8
-- title:
--   OAI.UniversalTensorSquare.degreeTree20_6All: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.degreeTree20_6All` of [lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeTreeProof20.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeTreeProof20.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Balance Saxl.Columns`):
--
--   ```lean
--   lemma degreeTree20_6All : degreeTree20_6.All (RowSquare [7,5,2,2,2,1,1])
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowTree.All` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split); `OAI.UniversalTensorSquare.degreeTree20_6` (definitions bundle `OAIQ259US008` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.degree_pos20` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeTreeProof20.lean (declaration OAI.UniversalTensorSquare.degreeTree20_6All)

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US008

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

lemma degreeTree20_6All : degreeTree20_6.All (RowSquare [7,5,2,2,2,1,1]) := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
