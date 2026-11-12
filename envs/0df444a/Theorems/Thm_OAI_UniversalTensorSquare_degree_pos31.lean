-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_degree_pos31
-- name    : OAI.UniversalTensorSquare.degree_pos31
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T20:21:18.632203+00:00
-- url     : https://prove2.me/theorems/cfd3c528-9acf-43ec-8d54-82d31c85e299
-- title:
--   OAI.UniversalTensorSquare.degree_pos31: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.degree_pos31` of [lean/OAI/RepresentationTheory/UniversalSquare/Finite/NumericalDegree31.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/NumericalDegree31.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Balance Saxl.Columns`):
--
--   ```lean
--   lemma degree_pos31 (μ : YoungDiagram) (hμ : μ.card = 31) :
--       0 < kronecker (canonicalTableau (candidate 6 2 1) degreeCard31)
--         (canonicalTableau (candidate 6 2 1) degreeCard31) (canonicalTableau μ hμ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.candidate` and `OAI.UniversalTensorSquare.degreeCard31` (definitions bundle `OAIQ259US007` of this split); `OAI.Saxl.canonicalTableau` and `OAI.Saxl.kronecker` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.universal_partition_le64` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/NumericalDegree31.lean (declaration OAI.UniversalTensorSquare.degree_pos31)

import Mathlib
import Definitions.Def_UniversalTensorSquares
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
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos31 (μ : YoungDiagram) (hμ : μ.card = 31) :
    0 < kronecker (canonicalTableau (candidate 6 2 1) degreeCard31)
      (canonicalTableau (candidate 6 2 1) degreeCard31) (canonicalTableau μ hμ) := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
