-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_residualProperty_sound
-- name    : OAI.UniversalTensorSquare.residualProperty_sound
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T20:23:09.116825+00:00
-- url     : https://prove2.me/theorems/c2dc5804-2fc3-46c9-853c-b5a03dc21359
-- title:
--   OAI.UniversalTensorSquare.residualProperty_sound: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.residualProperty_sound` of [lean/OAI/RepresentationTheory/UniversalSquare/Support/NumericalSupport.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/NumericalSupport.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Balance Saxl.Columns`):
--
--   ```lean
--   lemma residualProperty_sound {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
--       (hn : (candidate M b δ).card = n) (hre : r = 2*b+δ)
--       {qs ls : List (List ℕ)}
--       (hcones : ∀ q ∈ qs, ∀ μ : YoungDiagram, μ.card = n →
--         RowsDom μ.rowLens q → SquareOccurs (candidate M b δ) μ)
--       (hlists : ∀ rs ∈ ls, SquareOccurs (candidate M b δ) (rowDiagram rs))
--       {rs : List ℕ} (hgood : GoodRows rs) (hsum : rs.sum = n)
--       (h : ResidualProperty M r qs ls rs) : SquareOccurs (candidate M b δ) (rowDiagram rs)
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.GoodRows`, `OAI.UniversalTensorSquare.ResidualProperty`, `OAI.UniversalTensorSquare.RowsDom` and `OAI.UniversalTensorSquare.rowDiagram` (definitions bundle `OAIQ259US001` of this split); `OAI.UniversalTensorSquare.SquareOccurs` and `OAI.UniversalTensorSquare.candidate` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degree_pos112`, `OAI.UniversalTensorSquare.degree_pos118`, `OAI.UniversalTensorSquare.degree_pos12`, `OAI.UniversalTensorSquare.degree_pos14`, `OAI.UniversalTensorSquare.degree_pos151`, `OAI.UniversalTensorSquare.degree_pos16`, `OAI.UniversalTensorSquare.degree_pos18`, `OAI.UniversalTensorSquare.degree_pos19`, `OAI.UniversalTensorSquare.degree_pos20`, `OAI.UniversalTensorSquare.degree_pos22`, `OAI.UniversalTensorSquare.degree_pos24`, `OAI.UniversalTensorSquare.degree_pos26`, `OAI.UniversalTensorSquare.degree_pos31`, `OAI.UniversalTensorSquare.degree_pos32`, `OAI.UniversalTensorSquare.degree_pos33`, `OAI.UniversalTensorSquare.degree_pos34`, `OAI.UniversalTensorSquare.degree_pos35`, `OAI.UniversalTensorSquare.degree_pos37`, `OAI.UniversalTensorSquare.degree_pos38`, `OAI.UniversalTensorSquare.degree_pos39`, `OAI.UniversalTensorSquare.degree_pos41`, `OAI.UniversalTensorSquare.degree_pos43`, `OAI.UniversalTensorSquare.degree_pos44`, `OAI.UniversalTensorSquare.degree_pos46`, `OAI.UniversalTensorSquare.degree_pos48`, `OAI.UniversalTensorSquare.degree_pos50`, `OAI.UniversalTensorSquare.degree_pos52`, `OAI.UniversalTensorSquare.degree_pos53`, `OAI.UniversalTensorSquare.degree_pos54`, `OAI.UniversalTensorSquare.degree_pos56`, `OAI.UniversalTensorSquare.degree_pos57`, `OAI.UniversalTensorSquare.degree_pos58`, `OAI.UniversalTensorSquare.degree_pos59`, `OAI.UniversalTensorSquare.degree_pos60`, `OAI.UniversalTensorSquare.degree_pos61`, `OAI.UniversalTensorSquare.degree_pos62`, `OAI.UniversalTensorSquare.degree_pos64`, `OAI.UniversalTensorSquare.degree_pos89`, `OAI.UniversalTensorSquare.universal_partition_exceptional` and `OAI.UniversalTensorSquare.universal_partition_le64` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/NumericalSupport.lean (declaration OAI.UniversalTensorSquare.residualProperty_sound)

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
open Saxl Saxl.Balance Saxl.Columns

lemma residualProperty_sound {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (hn : (candidate M b δ).card = n) (hre : r = 2*b+δ)
    {qs ls : List (List ℕ)}
    (hcones : ∀ q ∈ qs, ∀ μ : YoungDiagram, μ.card = n →
      RowsDom μ.rowLens q → SquareOccurs (candidate M b δ) μ)
    (hlists : ∀ rs ∈ ls, SquareOccurs (candidate M b δ) (rowDiagram rs))
    {rs : List ℕ} (hgood : GoodRows rs) (hsum : rs.sum = n)
    (h : ResidualProperty M r qs ls rs) : SquareOccurs (candidate M b δ) (rowDiagram rs) := by
  sorry

end UniversalTensorSquare

end
end

end OAI
end
