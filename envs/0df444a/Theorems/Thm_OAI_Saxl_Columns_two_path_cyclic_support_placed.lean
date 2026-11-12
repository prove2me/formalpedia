-- Prove2me | Theorems.Thm_OAI_Saxl_Columns_two_path_cyclic_support_placed
-- name    : OAI.Saxl.Columns.two_path_cyclic_support_placed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T18:10:13.457485+00:00
-- url     : https://prove2.me/theorems/92c0dc31-5c35-4b82-9bd5-dbee3f7a0749
-- title:
--   OAI.Saxl.Columns.two_path_cyclic_support_placed: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Saxl.Columns.two_path_cyclic_support_placed` of [lean/OAI/RepresentationTheory/UniversalSquare/Contraction/TwoPathContraction.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Contraction/TwoPathContraction.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Saxl.Columns`):
--
--   ```lean
--   theorem two_path_cyclic_support_placed {n : ℕ} (p r : ℕ) (rs : List ℕ)
--       (hp : 2*p+1 ≤ 4) (hrs : ∀ a ∈ rs, 1 ≤ a ∧ a ≤ 4)
--       (hr : rs.sum = 2*r+1) (μ : YoungDiagram)
--       (hc : ((2*p+1)::rs).Perm μ.transpose.rowLens)
--       (t : Tableau n μ) (e : Fin n ≃ Fin (2*p+1) ⊕ Fin (2*r+1)) :
--       ∃ F : Representation.IntertwiningMap (spechtRep t)
--         (cyclic (wordRep n 4)
--           (positionProduct e (Path.bandWord p) (Path.bandWord r))).toRepresentation,
--         F ≠ 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.positionProduct` (definitions bundle `OAIQ259US000` of this split); `OAI.Saxl.Path.bandWord` (definitions bundle `OAIQ259US001` of this split); `OAI.Saxl.Specht`, `OAI.Saxl.Tableau`, `OAI.Saxl.WordSpace`, `OAI.Saxl.cyclic`, `OAI.Saxl.spechtRep` and `OAI.Saxl.wordRep` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proofs of `OAI.Saxl.Balance.PackingPlan.realize`, `OAI.Saxl.Balance.balancePacking` and `OAI.Saxl.Balance.short_pair_support` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Contraction/TwoPathContraction.lean (declaration OAI.Saxl.Columns.two_path_cyclic_support_placed)

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US000
import Definitions.Def_OAIQ259US001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace Saxl.Columns

theorem two_path_cyclic_support_placed {n : ℕ} (p r : ℕ) (rs : List ℕ)
    (hp : 2*p+1 ≤ 4) (hrs : ∀ a ∈ rs, 1 ≤ a ∧ a ≤ 4)
    (hr : rs.sum = 2*r+1) (μ : YoungDiagram)
    (hc : ((2*p+1)::rs).Perm μ.transpose.rowLens)
    (t : Tableau n μ) (e : Fin n ≃ Fin (2*p+1) ⊕ Fin (2*r+1)) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n 4)
        (positionProduct e (Path.bandWord p) (Path.bandWord r))).toRepresentation,
      F ≠ 0 := by
  sorry

end Saxl.Columns
end
end

end OAI
end
