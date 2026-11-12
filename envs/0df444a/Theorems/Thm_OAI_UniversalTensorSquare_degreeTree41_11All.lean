-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_degreeTree41_11All
-- name    : OAI.UniversalTensorSquare.degreeTree41_11All
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T18:51:27.641537+00:00
-- url     : https://prove2.me/theorems/e497f137-86d6-4420-aa1d-24152faf7de3
-- title:
--   OAI.UniversalTensorSquare.degreeTree41_11All: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.degreeTree41_11All` of [lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeTreeProof41.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeTreeProof41.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Balance Saxl.Columns`):
--
--   ```lean
--   lemma degreeTree41_11All : degreeTree41_11.All (RowSquare [11,10,4,3,2,2,2,2,2,2,1])
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowTree.All` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split); `OAI.UniversalTensorSquare.degreeTree41_11` (definitions bundle `OAIQ259US009` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.degreeTree41_12All` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeTreeProof41.lean (declaration OAI.UniversalTensorSquare.degreeTree41_11All)

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US009

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

lemma degreeTree41_11All : degreeTree41_11.All (RowSquare [11,10,4,3,2,2,2,2,2,2,1]) := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
