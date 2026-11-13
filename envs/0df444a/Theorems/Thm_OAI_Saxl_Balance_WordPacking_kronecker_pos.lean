-- Prove2me | Theorems.Thm_OAI_Saxl_Balance_WordPacking_kronecker_pos
-- name    : OAI.Saxl.Balance.WordPacking.kronecker_pos
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T18:14:00.804756+00:00
-- url     : https://prove2.me/theorems/2964a72e-138f-45cb-b513-195178802364
-- title:
--   OAI.Saxl.Balance.WordPacking.kronecker_pos: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Saxl.Balance.WordPacking.kronecker_pos` of [lean/OAI/RepresentationTheory/UniversalSquare/Balance/WordPacking.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Balance/WordPacking.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Saxl.Balance`, with `open scoped BigOperators`, `open FlagColumns Columns`):
--
--   ```lean
--   theorem WordPacking.kronecker_pos {rs ps : List ℕ} {lam μ : YoungDiagram}
--       (a : Tableau rs.sum lam) (t : Tableau rs.sum μ)
--       {A : Fin (lam.colLen 0 * lam.colLen 0) → Prop}
--       {label : Fin (lam.colLen 0 * lam.colLen 0) → ℕ} {marks : Finset ℕ}
--       (P : WordPacking rs ps (lam.colLen 0) A label marks)
--       (hv : blocks rs (standard (lam.colLen 0)) = polytabloid a)
--       (hp : ∀ p ∈ ps, 0 < p)
--       (ho : ∀ x y, A x → A y → label x < label y → output x < output y)
--       (hd : Dominates μ (columnShape ps).transpose) : 0 < kronecker a a t
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Balance.output` (definitions bundle `OAIQ259US000` of this split); `OAI.Saxl.Dominates`, `OAI.Saxl.Columns.columnShape` and `OAI.Saxl.FlagColumns.standard` (definitions bundle `OAIQ259US001` of this split); `OAI.Saxl.Balance.WordPacking` and `OAI.Saxl.FlagColumns.blocks` (definitions bundle `OAIQ259US006` of this split); `OAI.Saxl.Tableau`, `OAI.Saxl.WordSpace`, `OAI.Saxl.kronecker` and `OAI.Saxl.polytabloid` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.exceptional_pos106`, `OAI.UniversalTensorSquare.exceptional_pos108`, `OAI.UniversalTensorSquare.exceptional_pos110`, `OAI.UniversalTensorSquare.exceptional_pos114`, `OAI.UniversalTensorSquare.exceptional_pos149`, `OAI.UniversalTensorSquare.exceptional_pos71`, `OAI.UniversalTensorSquare.exceptional_pos75`, `OAI.UniversalTensorSquare.exceptional_pos79`, `OAI.UniversalTensorSquare.exceptional_pos81`, `OAI.UniversalTensorSquare.exceptional_pos83`, `OAI.UniversalTensorSquare.exceptional_pos85`, `OAI.UniversalTensorSquare.exceptional_pos87`, `OAI.UniversalTensorSquare.packingPlan_pos`, `OAI.UniversalTensorSquare.universal_partition_exceptional` and `OAI.UniversalTensorSquares.universal_tensor_square` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Balance/WordPacking.lean (declaration OAI.Saxl.Balance.WordPacking.kronecker_pos)

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace Saxl
open scoped BigOperators

namespace Balance
open FlagColumns Columns

theorem WordPacking.kronecker_pos {rs ps : List ℕ} {lam μ : YoungDiagram}
    (a : Tableau rs.sum lam) (t : Tableau rs.sum μ)
    {A : Fin (lam.colLen 0 * lam.colLen 0) → Prop}
    {label : Fin (lam.colLen 0 * lam.colLen 0) → ℕ} {marks : Finset ℕ}
    (P : WordPacking rs ps (lam.colLen 0) A label marks)
    (hv : blocks rs (standard (lam.colLen 0)) = polytabloid a)
    (hp : ∀ p ∈ ps, 0 < p)
    (ho : ∀ x y, A x → A y → label x < label y → output x < output y)
    (hd : Dominates μ (columnShape ps).transpose) : 0 < kronecker a a t := by
  sorry

end Balance
end Saxl
end
end

end OAI
end
