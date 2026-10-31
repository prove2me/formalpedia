-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_injectiveInduced_invariant_tensor
-- name    : OAI.NuclearUltrapower.injectiveInduced_invariant_tensor
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T07:08:24.845309+00:00
-- url     : https://prove2.me/theorems/c272cd5e-8267-4bff-b2ee-d6e60a06dd71
-- title:
--   OAI.NuclearUltrapower.injectiveInduced_invariant_tensor: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.injectiveInduced_invariant_tensor` of [lean/OAI/Analysis/NuclearUltrapower/GroupObstruction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/GroupObstruction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower`, with `open scoped TensorProduct InnerProductSpace`):
--
--   ```lean
--   theorem injectiveInduced_invariant_tensor :
--       ∃ z : InjectiveInducedSpace f π ⊗[ℂ] π.dual, z ≠ 0 ∧
--         ∀ g : Γ, TensorProduct.congrIsometry (injectiveInduced f hf π (f g))
--           (π.dual.action g) z = z
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.FiniteUnitaryRep` (definitions bundle `OAIQ019N001` of this split); `OAI.NuclearUltrapower.InjectiveInducedSpace` and `OAI.NuclearUltrapower.injectiveInduced` (definitions bundle `OAIQ019N043` of this split); `OAI.NuclearUltrapower.FiniteUnitaryRep.dual` (definitions bundle `OAIQ019N047` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.fullGroup_no_nuclear_ultrapower` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/GroupObstruction.lean (declaration OAI.NuclearUltrapower.injectiveInduced_invariant_tensor)

import Mathlib
import Definitions.Def_OAIQ019N043

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped TensorProduct InnerProductSpace
namespace NuclearUltrapower
universe u v w
section InjectiveInduction
variable {Γ : Type u} {Δ : Type v} [Group Γ] [Group Δ]
  (f : Γ →* Δ) (hf : Function.Injective f) (π : FiniteUnitaryRep.{u,w} Γ)

theorem injectiveInduced_invariant_tensor :
    ∃ z : InjectiveInducedSpace f π ⊗[ℂ] π.dual, z ≠ 0 ∧
      ∀ g : Γ, TensorProduct.congrIsometry (injectiveInduced f hf π (f g))
        (π.dual.action g) z = z := by
  sorry

end InjectiveInduction
end NuclearUltrapower
end
end

end OAI
end
