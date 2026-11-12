-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_degreeDiagramRegionsChecked31
-- name    : OAI.UniversalTensorSquare.degreeDiagramRegionsChecked31
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T18:27:22.837635+00:00
-- url     : https://prove2.me/theorems/ac383ef0-0ba2-4e0b-b8bf-21a40ae046a5
-- title:
--   OAI.UniversalTensorSquare.degreeDiagramRegionsChecked31: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.degreeDiagramRegionsChecked31` of [lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeRegions31.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeRegions31.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`):
--
--   ```lean
--   lemma degreeDiagramRegionsChecked31 : ∀ R ∈ degreeRegions31,
--       ∀ μ : YoungDiagram, μ.card = 31 → RowBounds μ.transpose R.1 →
--         RowBounds μ R.2 → degreeP31 μ.rowLens
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.PrefixRegion` and `OAI.UniversalTensorSquare.RowBounds` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.degreeP31` (definitions bundle `OAIQ259US008` of this split); `OAI.UniversalTensorSquare.degreeRegions31` (definitions bundle `OAIQ259US012` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.degreeCheck31` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeRegions31.lean (declaration OAI.UniversalTensorSquare.degreeDiagramRegionsChecked31)

import Mathlib
import Definitions.Def_OAIQ259US008
import Definitions.Def_OAIQ259US012

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniversalTensorSquare

lemma degreeDiagramRegionsChecked31 : ∀ R ∈ degreeRegions31,
    ∀ μ : YoungDiagram, μ.card = 31 → RowBounds μ.transpose R.1 →
      RowBounds μ R.2 → degreeP31 μ.rowLens := by
  sorry

end UniversalTensorSquare
end

end OAI
end
