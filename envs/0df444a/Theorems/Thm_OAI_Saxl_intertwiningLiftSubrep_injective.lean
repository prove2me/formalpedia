-- Prove2me | Theorems.Thm_OAI_Saxl_intertwiningLiftSubrep_injective
-- name    : OAI.Saxl.intertwiningLiftSubrep_injective
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-15T21:31:23.833415+00:00
-- url     : https://prove2.me/theorems/1392ec74-0bef-45ab-ba76-440445502db1
-- title:
--   OAI.Saxl.intertwiningLiftSubrep_injective: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Saxl.intertwiningLiftSubrep_injective` of [lean/OAI/RepresentationTheory/Saxl/CyclicTensor.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/Saxl/CyclicTensor.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Saxl`, with `open scoped TensorProduct`):
--
--   ```lean
--   lemma intertwiningLiftSubrep_injective {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [AddCommGroup X] [Module ℂ X]
--       [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
--       (f : Representation.IntertwiningMap ρ σ) (hf : Function.Injective f)
--       (S : Subrepresentation σ) (hS : S ≤ f.range) :
--       Function.Injective (intertwiningLiftSubrep f hf S hS)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.intertwiningLiftSubrep` (definitions bundle `OAIQ259US000` of this split).
--
--   **Used by.** The proof of `OAI.Saxl.kronecker_pos_of_contraction` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/Saxl/CyclicTensor.lean (declaration OAI.Saxl.intertwiningLiftSubrep_injective)

import Mathlib
import Definitions.Def_OAIQ259US000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uX uY

namespace Saxl

lemma intertwiningLiftSubrep_injective {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Injective f)
    (S : Subrepresentation σ) (hS : S ≤ f.range) :
    Function.Injective (intertwiningLiftSubrep f hf S hS) := by
  sorry

end Saxl

end

end OAI
end
