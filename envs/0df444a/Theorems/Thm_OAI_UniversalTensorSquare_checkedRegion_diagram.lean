-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_checkedRegion_diagram
-- name    : OAI.UniversalTensorSquare.checkedRegion_diagram
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T10:53:56.356451+00:00
-- url     : https://prove2.me/theorems/f6040d13-a276-41f4-a24b-b5a9cbbe7ffb
-- title:
--   OAI.UniversalTensorSquare.checkedRegion_diagram: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.checkedRegion_diagram` of [lean/OAI/RepresentationTheory/UniversalSquare/Support/UnionRowChecker.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/UnionRowChecker.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`):
--
--   ```lean
--   lemma checkedRegion_diagram {n M r H W : ℕ} {qs : List (List ℕ)} {t : RowTree}
--       {regions : List PrefixRegion}
--       (check : ∀ h ≤ H, checkRegionPrefixes (quickResidual M r qs t) h n W regions [] = true)
--       (μ : YoungDiagram) (hn : μ.card = n) {A B : List (ℕ × ℕ)}
--       (hR : (A,B) ∈ regions) (hA : RowBounds μ.transpose A) (hB : RowBounds μ B)
--       (hH : firstBound n A ≤ H) (hW : firstBound n B ≤ W) :
--       TreeResidual M r qs t μ.rowLens
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.PrefixRegion`, `OAI.UniversalTensorSquare.RowBounds`, `OAI.UniversalTensorSquare.RowTree`, `OAI.UniversalTensorSquare.TreeResidual` and `OAI.UniversalTensorSquare.checkRegionPrefixes` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.firstBound` (definitions bundle `OAIQ259US002` of this split); `OAI.UniversalTensorSquare.quickResidual` (definitions bundle `OAIQ259US022` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeCheck14`, `OAI.UniversalTensorSquare.degreeCheck35`, `OAI.UniversalTensorSquare.degreeDiagramRegionsChecked22`, `OAI.UniversalTensorSquare.degreeDiagramRegionsChecked24`, `OAI.UniversalTensorSquare.degreeDiagramRegionsChecked31`, `OAI.UniversalTensorSquare.degreeDiagramRegionsChecked37`, `OAI.UniversalTensorSquare.degreeDiagramRegionsChecked39`, `OAI.UniversalTensorSquare.degreeDiagramRegionsChecked58`, `OAI.UniversalTensorSquare.degree_pos26`, `OAI.UniversalTensorSquare.degree_pos41`, `OAI.UniversalTensorSquare.degree_pos43`, `OAI.UniversalTensorSquare.degree_pos62` and `OAI.UniversalTensorSquare.degree_pos64` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/UnionRowChecker.lean (declaration OAI.UniversalTensorSquare.checkedRegion_diagram)

import Mathlib
import Definitions.Def_OAIQ259US022

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniversalTensorSquare

lemma checkedRegion_diagram {n M r H W : ℕ} {qs : List (List ℕ)} {t : RowTree}
    {regions : List PrefixRegion}
    (check : ∀ h ≤ H, checkRegionPrefixes (quickResidual M r qs t) h n W regions [] = true)
    (μ : YoungDiagram) (hn : μ.card = n) {A B : List (ℕ × ℕ)}
    (hR : (A,B) ∈ regions) (hA : RowBounds μ.transpose A) (hB : RowBounds μ B)
    (hH : firstBound n A ≤ H) (hW : firstBound n B ≤ W) :
    TreeResidual M r qs t μ.rowLens := by
  sorry

end UniversalTensorSquare
end

end OAI
end
