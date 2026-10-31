-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_residual_value_native
-- name    : OAI.NuclearUltrapower.SOS.ElementarySpectral.residual_value_native
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T07:41:33.592013+00:00
-- url     : https://prove2.me/theorems/592c1e53-2cd0-4d2a-8dbf-edb0d1b8d782
-- title:
--   OAI.NuclearUltrapower.SOS.ElementarySpectral.residual_value_native: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.SOS.ElementarySpectral.residual_value_native` of [lean/OAI/Analysis/NuclearUltrapower/IntegralCertificate.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/IntegralCertificate.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.SOS.ElementarySpectral`):
--
--   ```lean
--   theorem residual_value_native (ρ : E →* (H ≃ₗᵢ[ℂ] H)) :
--       eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) residual =
--         (10000000000000 : ℤ) • (eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) delta *
--           eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) delta) -
--         (1000000000000 : ℤ) • eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) delta -
--         (10 : ℤ) • gramValue (value (A := H →L[ℂ] H) (unitaryRep ρ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.SOS.Mat3` and `OAI.NuclearUltrapower.SOS.eval` (definitions bundle `OAIQ019N000` of this split); `OAI.NuclearUltrapower.SOS.SL` (definitions bundle `OAIQ019N001` of this split); `OAI.NuclearUltrapower.SOS.gramValue` and `OAI.NuclearUltrapower.SOS.ElementarySpectral.value` (definitions bundle `OAIQ019N044` of this split); `OAI.NuclearUltrapower.SOS.delta` (definitions bundle `OAIQ019N047` of this split); `OAI.NuclearUltrapower.SOS.E`, `OAI.NuclearUltrapower.SOS.residual` and `OAI.NuclearUltrapower.SOS.ElementarySpectral.unitaryRep` (definitions bundle `OAIQ019N049` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_certificate` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/IntegralCertificate.lean (declaration OAI.NuclearUltrapower.SOS.ElementarySpectral.residual_value_native)

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
namespace NuclearUltrapower.SOS
namespace ElementarySpectral
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
attribute [local irreducible] gramValue eval residual

theorem residual_value_native (ρ : E →* (H ≃ₗᵢ[ℂ] H)) :
    eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) residual =
      (10000000000000 : ℤ) • (eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) delta *
        eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) delta) -
      (1000000000000 : ℤ) • eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) delta -
      (10 : ℤ) • gramValue (value (A := H →L[ℂ] H) (unitaryRep ρ)) := by
  sorry
end ElementarySpectral
end NuclearUltrapower.SOS
end
end

end OAI
end
