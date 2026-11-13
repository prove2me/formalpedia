-- Prove2me | Theorems.Thm_OAI_Saxl_vector_of_invariant_functional_uts
-- name    : OAI.Saxl.vector_of_invariant_functional_uts
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T04:10:15.560195+00:00
-- url     : https://prove2.me/theorems/20726513-06e6-429f-a58d-a865c623156b
-- title:
--   OAI.Saxl.vector_of_invariant_functional_uts: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Saxl.vector_of_invariant_functional` of [lean/OAI/RepresentationTheory/Saxl/YoungRule.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/Saxl/YoungRule.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Saxl`, with `open scoped TensorProduct`):
--
--   ```lean
--   lemma vector_of_invariant_functional_uts {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
--       (a : Fin n → Fin d) (l : Module.Dual ℂ (Specht t)) (hl : l ≠ 0)
--       (he : ∀ g : Equiv.Perm (Fin n), a ∘ g = a → ∀ x, l (spechtRep t g x) = l x) :
--       ∃ y : Specht t, y ≠ 0 ∧ ∀ g : Equiv.Perm (Fin n), a ∘ g = a → spechtRep t g y = y
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Specht`, `OAI.Saxl.Tableau`, `OAI.Saxl.WordSpace` and `OAI.Saxl.spechtRep` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proof of `OAI.Saxl.young_orbit_map_uts` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/Saxl/YoungRule.lean (declaration OAI.Saxl.vector_of_invariant_functional)

import Mathlib
import Definitions.Def_UniversalTensorSquares

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

lemma vector_of_invariant_functional_uts {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (a : Fin n → Fin d) (l : Module.Dual ℂ (Specht t)) (hl : l ≠ 0)
    (he : ∀ g : Equiv.Perm (Fin n), a ∘ g = a → ∀ x, l (spechtRep t g x) = l x) :
    ∃ y : Specht t, y ≠ 0 ∧ ∀ g : Equiv.Perm (Fin n), a ∘ g = a → spechtRep t g y = y := by
  sorry

end Saxl

end

end OAI
end
