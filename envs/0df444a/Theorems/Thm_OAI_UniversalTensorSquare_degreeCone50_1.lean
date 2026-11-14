-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_degreeCone50_1
-- name    : OAI.UniversalTensorSquare.degreeCone50_1
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T13:37:13.04621+00:00
-- url     : https://prove2.me/theorems/72e10025-d782-4dc6-aa2d-d6e85b9e296c
-- title:
--   OAI.UniversalTensorSquare.degreeCone50_1: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.degreeCone50_1` of [lean/OAI/RepresentationTheory/UniversalSquare/Finite/NumericalDegree50.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/NumericalDegree50.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Balance Saxl.Columns`):
--
--   ```lean
--   lemma degreeCone50_1 (μ : YoungDiagram) (hμ : μ.card = 50)
--       (hd : RowsDom μ.rowLens degreeRows50_1) : SquareOccurs (candidate 8 3 1) μ
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowsDom` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.degreeRows50_1` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.SquareOccurs` and `OAI.UniversalTensorSquare.candidate` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.degree_pos50` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/NumericalDegree50.lean (declaration OAI.UniversalTensorSquare.degreeCone50_1)

import Mathlib
import Definitions.Def_OAIQ259US002
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

lemma degreeCone50_1 (μ : YoungDiagram) (hμ : μ.card = 50)
    (hd : RowsDom μ.rowLens degreeRows50_1) : SquareOccurs (candidate 8 3 1) μ := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
