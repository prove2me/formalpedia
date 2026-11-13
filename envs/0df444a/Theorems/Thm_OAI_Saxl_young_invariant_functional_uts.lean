-- Prove2me | Theorems.Thm_OAI_Saxl_young_invariant_functional_uts
-- name    : OAI.Saxl.young_invariant_functional_uts
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T04:12:29.215211+00:00
-- url     : https://prove2.me/theorems/a1f499a9-05b3-4ce8-a82d-bc40ed33d647
-- title:
--   OAI.Saxl.young_invariant_functional_uts: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Saxl.young_invariant_functional` of [lean/OAI/RepresentationTheory/Saxl/YoungRule.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/Saxl/YoungRule.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Saxl`, with `open scoped TensorProduct`):
--
--   ```lean
--   theorem young_invariant_functional_uts (θ τ : YoungDiagram)
--       (hc : τ.card = θ.card) (hd : Dominates τ θ) :
--       ∃ (a : Fin τ.card → Fin (θ.colLen 0)) (l : Module.Dual ℂ (Specht (shapeTableau τ))),
--         l ≠ 0 ∧
--         (∀ j, (Finset.univ.filter (fun i => a i = j)).card = θ.rowLen j) ∧
--         (∀ g : Equiv.Perm (Fin τ.card), a ∘ g = a →
--           ∀ x, l (spechtRep (shapeTableau τ) g x) = l x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Dominates` (definitions bundle `OAIQ259US001` of this split); `OAI.Saxl.shapeTableau` (definitions bundle `OAIQ259US007` of this split); `OAI.Saxl.Specht`, `OAI.Saxl.WordSpace` and `OAI.Saxl.spechtRep` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proof of `OAI.Saxl.young_orbit_map_uts` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/Saxl/YoungRule.lean (declaration OAI.Saxl.young_invariant_functional)

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

theorem young_invariant_functional_uts (θ τ : YoungDiagram)
    (hc : τ.card = θ.card) (hd : Dominates τ θ) :
    ∃ (a : Fin τ.card → Fin (θ.colLen 0)) (l : Module.Dual ℂ (Specht (shapeTableau τ))),
      l ≠ 0 ∧
      (∀ j, (Finset.univ.filter (fun i => a i = j)).card = θ.rowLen j) ∧
      (∀ g : Equiv.Perm (Fin τ.card), a ∘ g = a →
        ∀ x, l (spechtRep (shapeTableau τ) g x) = l x) := by
  sorry

end Saxl

end

end OAI
end
