-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_degreeTree43_154All
-- name    : OAI.UniversalTensorSquare.degreeTree43_154All
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T19:01:17.068354+00:00
-- url     : https://prove2.me/theorems/bca2fcc1-49f1-48c7-9804-92f9a7aa192a
-- title:
--   OAI.UniversalTensorSquare.degreeTree43_154All: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.degreeTree43_154All` of [lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeTreeProof43.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeTreeProof43.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Balance Saxl.Columns`):
--
--   ```lean
--   lemma degreeTree43_154All : degreeTree43_154.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1])
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowTree.All` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split); `OAI.UniversalTensorSquare.degreeTree43_154` (definitions bundle `OAIQ259US009` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.degreeTree43_159All` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeTreeProof43.lean (declaration OAI.UniversalTensorSquare.degreeTree43_154All)

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

lemma degreeTree43_154All : degreeTree43_154.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
