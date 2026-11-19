-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_degree_pos13
-- name    : OAI.UniversalTensorSquare.degree_pos13
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-18T14:05:55.721768+00:00
-- url     : https://prove2.me/theorems/7d0a2926-2888-46e9-a80c-7802fbba7504
-- title:
--   OAI.UniversalTensorSquare.degree_pos13: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.degree_pos13` of [lean/OAI/RepresentationTheory/UniversalSquare/Finite/NumericalDegree13.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/NumericalDegree13.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma degree_pos13 (μ : YoungDiagram) (hμ : μ.card = 13) :
--       0 < kronecker (canonicalTableau (rowDiagram [4,4,3,2]) degreeCard13)
--         (canonicalTableau (rowDiagram [4,4,3,2]) degreeCard13) (canonicalTableau μ hμ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.rowDiagram` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.degreeCard13` (definitions bundle `OAIQ259US021` of this split); `OAI.Saxl.canonicalTableau` and `OAI.Saxl.kronecker` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.universal_partition_le64` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/NumericalDegree13.lean (declaration OAI.UniversalTensorSquare.degree_pos13)

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
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma degree_pos13 (μ : YoungDiagram) (hμ : μ.card = 13) :
    0 < kronecker (canonicalTableau (rowDiagram [4,4,3,2]) degreeCard13)
      (canonicalTableau (rowDiagram [4,4,3,2]) degreeCard13) (canonicalTableau μ hμ) := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
