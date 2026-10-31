-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_exists_fixed_nearby
-- name    : OAI.NuclearUltrapower.SOS.ElementarySpectral.exists_fixed_nearby
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T07:39:45.359602+00:00
-- url     : https://prove2.me/theorems/7dc09719-3438-42b8-bd95-7c7e5d0eaa23
-- title:
--   OAI.NuclearUltrapower.SOS.ElementarySpectral.exists_fixed_nearby: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.SOS.ElementarySpectral.exists_fixed_nearby` of [lean/OAI/Analysis/NuclearUltrapower/Kazhdan.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/Kazhdan.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.SOS.ElementarySpectral`, with `open scoped InnerProductSpace`):
--
--   ```lean
--   theorem exists_fixed_nearby (ρ : E →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
--       ∃ y : H, (∀ g : E, ρ g y = y) ∧
--         (1/10 : ℝ) * ‖x-y‖ ^ 2 ≤ SOSEnergy.energy eGenSet ρ x
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.SOS.SL` (definitions bundle `OAIQ019N001` of this split); `OAI.NuclearUltrapower.SOSEnergy.energy` (definitions bundle `OAIQ019N016` of this split); `OAI.NuclearUltrapower.SOS.eGenSet` (definitions bundle `OAIQ019N044` of this split); `OAI.NuclearUltrapower.SOS.E` (definitions bundle `OAIQ019N049` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.main_statement` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/Kazhdan.lean (declaration OAI.NuclearUltrapower.SOS.ElementarySpectral.exists_fixed_nearby)

import Mathlib
import Definitions.Def_OAIQ019N044

section

attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.supportComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower.SOS.ElementarySpectral
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_fixed_nearby (ρ : E →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
    ∃ y : H, (∀ g : E, ρ g y = y) ∧
      (1/10 : ℝ) * ‖x-y‖ ^ 2 ≤ SOSEnergy.energy eGenSet ρ x := by
  sorry

end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end
