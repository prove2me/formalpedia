-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_delta_energy
-- name    : OAI.NuclearUltrapower.SOS.ElementarySpectral.delta_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T07:57:11.032599+00:00
-- url     : https://prove2.me/theorems/3952a058-c5e8-487a-8c3b-8eb694b6213f
-- title:
--   OAI.NuclearUltrapower.SOS.ElementarySpectral.delta_energy: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.SOS.ElementarySpectral.delta_energy` of [lean/OAI/Analysis/NuclearUltrapower/SOSGap.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SOSGap.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.SOS.ElementarySpectral`, with `open scoped ComplexOrder InnerProductSpace`):
--
--   ```lean
--   theorem delta_energy (ρ : E →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
--       (inner ℂ x (eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) delta x)).re = SOSEnergy.energy eGenSet ρ x / 2
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.SOS.Mat3` and `OAI.NuclearUltrapower.SOS.eval` (definitions bundle `OAIQ019N000` of this split); `OAI.NuclearUltrapower.SOS.SL` (definitions bundle `OAIQ019N001` of this split); `OAI.NuclearUltrapower.SOSEnergy.energy` (definitions bundle `OAIQ019N016` of this split); `OAI.NuclearUltrapower.SOS.eGenSet` and `OAI.NuclearUltrapower.SOS.ElementarySpectral.value` (definitions bundle `OAIQ019N044` of this split); `OAI.NuclearUltrapower.SOS.delta` (definitions bundle `OAIQ019N047` of this split); `OAI.NuclearUltrapower.SOS.E` and `OAI.NuclearUltrapower.SOS.ElementarySpectral.unitaryRep` (definitions bundle `OAIQ019N049` of this split).
--
--   **Used by.** The proofs of `OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_gap`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_sq_gap` and `OAI.NuclearUltrapower.SOS.ElementarySpectral.exists_fixed_nearby` of this split import it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SOSGap.lean (declaration OAI.NuclearUltrapower.SOS.ElementarySpectral.delta_energy)

import Mathlib
import Definitions.Def_OAIQ019N044

section

attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped ComplexOrder InnerProductSpace
namespace NuclearUltrapower.SOS.ElementarySpectral

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem delta_energy (ρ : E →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
    (inner ℂ x (eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) delta x)).re = SOSEnergy.energy eGenSet ρ x / 2 := by
  sorry
end Hilbert
end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end
