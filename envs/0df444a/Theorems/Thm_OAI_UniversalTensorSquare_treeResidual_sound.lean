-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_treeResidual_sound
-- name    : OAI.UniversalTensorSquare.treeResidual_sound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T17:59:35.363554+00:00
-- url     : https://prove2.me/theorems/e6da46b6-2d3f-45b4-9dae-3f64908c1b4d
-- title:
--   OAI.UniversalTensorSquare.treeResidual_sound: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.treeResidual_sound` of [lean/OAI/RepresentationTheory/UniversalSquare/Support/ResidualTrees.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/ResidualTrees.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma treeResidual_sound {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
--       (hn : (candidate M b δ).card = n) (hre : r = 2*b+δ)
--       {qs : List (List ℕ)} {t : RowTree}
--       (hcones : ∀ q ∈ qs, ∀ μ : YoungDiagram, μ.card = n →
--         RowsDom μ.rowLens q → SquareOccurs (candidate M b δ) μ)
--       (htree : t.All (fun rs => SquareOccurs (candidate M b δ) (rowDiagram rs)))
--       {rs : List ℕ} (hgood : GoodRows rs) (hsum : rs.sum = n)
--       (h : TreeResidual M r qs t rs) : SquareOccurs (candidate M b δ) (rowDiagram rs)
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.GoodRows`, `OAI.UniversalTensorSquare.RowTree`, `OAI.UniversalTensorSquare.RowsDom`, `OAI.UniversalTensorSquare.TreeResidual`, `OAI.UniversalTensorSquare.rowDiagram` and `OAI.UniversalTensorSquare.RowTree.All` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.SquareOccurs` and `OAI.UniversalTensorSquare.candidate` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proof of `OAI.UniversalTensorSquare.universal_partition_exceptional` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/ResidualTrees.lean (declaration OAI.UniversalTensorSquare.treeResidual_sound)

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
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma treeResidual_sound {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (hn : (candidate M b δ).card = n) (hre : r = 2*b+δ)
    {qs : List (List ℕ)} {t : RowTree}
    (hcones : ∀ q ∈ qs, ∀ μ : YoungDiagram, μ.card = n →
      RowsDom μ.rowLens q → SquareOccurs (candidate M b δ) μ)
    (htree : t.All (fun rs => SquareOccurs (candidate M b δ) (rowDiagram rs)))
    {rs : List ℕ} (hgood : GoodRows rs) (hsum : rs.sum = n)
    (h : TreeResidual M r qs t rs) : SquareOccurs (candidate M b δ) (rowDiagram rs) := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
