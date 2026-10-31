-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_exists_norming_state
-- name    : OAI.NuclearUltrapower.exists_norming_state
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:05:19.502991+00:00
-- url     : https://prove2.me/theorems/1f90fd49-e4fe-4014-ac0b-22fba87b90d2
-- title:
--   OAI.NuclearUltrapower.exists_norming_state: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.exists_norming_state` of [lean/OAI/Analysis/NuclearUltrapower/FaithfulGNS.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/FaithfulGNS.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower`, with `open scoped ComplexOrder ENNReal`):
--
--   ```lean
--   theorem exists_norming_state (a : A) (ha : 0 ≤ a) :
--       ∃ f : A →ₚ[ℂ] ℂ, f 1 = 1 ∧ f a = (‖a‖ : ℂ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.gnsSpectralOrder` (definitions bundle `OAIQ019N020` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.universalGNS_injective` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/FaithfulGNS.lean (declaration OAI.NuclearUltrapower.exists_norming_state)

import Mathlib
import Definitions.Def_OAIQ019N020

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
universe u
open scoped ComplexOrder ENNReal
namespace NuclearUltrapower
variable {A : Type u} [CStarAlgebra A] [Nontrivial A]

attribute [local instance] OAI.NuclearUltrapower.gnsSpectralOrder
attribute [local instance] OAI.NuclearUltrapower.gnsSpectralOrderedRing
theorem exists_norming_state (a : A) (ha : 0 ≤ a) :
    ∃ f : A →ₚ[ℂ] ℂ, f 1 = 1 ∧ f a = (‖a‖ : ℂ) := by
  sorry

end NuclearUltrapower
end
end

end OAI
end
