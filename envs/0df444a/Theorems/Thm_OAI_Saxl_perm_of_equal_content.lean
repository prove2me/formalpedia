-- Prove2me | Theorems.Thm_OAI_Saxl_perm_of_equal_content
-- name    : OAI.Saxl.perm_of_equal_content
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T04:09:57.189139+00:00
-- url     : https://prove2.me/theorems/7d281a18-88c1-4102-9eff-0d255faafc10
-- title:
--   OAI.Saxl.perm_of_equal_content: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Saxl.perm_of_equal_content` of [lean/OAI/RepresentationTheory/Saxl/YoungRule.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/Saxl/YoungRule.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Saxl`, with `open scoped TensorProduct`):
--
--   ```lean
--   lemma perm_of_equal_content {n d : ℕ} (a b : Fin n → Fin d)
--       (h : ∀ j, (Finset.univ.filter (fun i => a i = j)).card =
--         (Finset.univ.filter (fun i => b i = j)).card) :
--       ∃ g : Equiv.Perm (Fin n), b ∘ g = a
--   ```
--
--   **Used by.** The proofs of `OAI_Saxl_young_orbit_map` and `OAI.Saxl.young_orbit_map_uts` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/Saxl/YoungRule.lean (declaration OAI.Saxl.perm_of_equal_content)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

lemma perm_of_equal_content {n d : ℕ} (a b : Fin n → Fin d)
    (h : ∀ j, (Finset.univ.filter (fun i => a i = j)).card =
      (Finset.univ.filter (fun i => b i = j)).card) :
    ∃ g : Equiv.Perm (Fin n), b ∘ g = a := by
  sorry

end Saxl

end

end OAI
end
