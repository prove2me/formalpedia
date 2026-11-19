-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_degreeDiagramRegionsChecked24
-- name    : OAI.UniversalTensorSquare.degreeDiagramRegionsChecked24
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:07:59.47154+00:00
-- url     : https://prove2.me/theorems/ca3bdd3d-c382-4464-8229-c24bbae6aecf
-- title:
--   OAI.UniversalTensorSquare.degreeDiagramRegionsChecked24: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.degreeDiagramRegionsChecked24` of [lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeRegions24.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeRegions24.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`):
--
--   ```lean
--   lemma degreeDiagramRegionsChecked24 : ∀ R ∈ degreeRegions24,
--       ∀ μ : YoungDiagram, μ.card = 24 → RowBounds μ.transpose R.1 →
--         RowBounds μ R.2 → degreeP24 μ.rowLens
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.PrefixRegion` and `OAI.UniversalTensorSquare.RowBounds` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.degreeP24` (definitions bundle `OAIQ259US008` of this split); `OAI.UniversalTensorSquare.degreeRegions24` (definitions bundle `OAIQ259US012` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.degreeCheck24` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Finite/DegreeRegions24.lean (declaration OAI.UniversalTensorSquare.degreeDiagramRegionsChecked24)

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

lemma degreeDiagramRegionsChecked24 : ∀ R ∈ degreeRegions24,
    ∀ μ : YoungDiagram, μ.card = 24 → RowBounds μ.transpose R.1 →
      RowBounds μ R.2 → degreeP24 μ.rowLens := by
  sorry

end UniversalTensorSquare
end

end OAI
end
