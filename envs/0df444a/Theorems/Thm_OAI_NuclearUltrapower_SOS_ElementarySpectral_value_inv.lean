-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_value_inv
-- name    : OAI.NuclearUltrapower.SOS.ElementarySpectral.value_inv
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T08:04:07.112226+00:00
-- url     : https://prove2.me/theorems/e0c01091-689d-4c5a-9868-1c8b6d946e4d
-- title:
--   OAI.NuclearUltrapower.SOS.ElementarySpectral.value_inv: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.SOS.ElementarySpectral.value_inv` of [lean/OAI/Analysis/NuclearUltrapower/SOSGap.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SOSGap.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.SOS.ElementarySpectral`, with `open scoped ComplexOrder InnerProductSpace`):
--
--   ```lean
--   theorem value_inv (ρ : E →* unitary A) {n : ℕ} (a : Mat3) (ha : GoodWord n a) :
--       value ρ (matInv a) = star (value ρ a)
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.SOS.Mat3` (definitions bundle `OAIQ019N000` of this split); `OAI.NuclearUltrapower.SOS.SL` (definitions bundle `OAIQ019N001` of this split); `OAI.NuclearUltrapower.SOS.GoodWord` and `OAI.NuclearUltrapower.SOS.ElementarySpectral.value` (definitions bundle `OAIQ019N044` of this split); `OAI.NuclearUltrapower.SOS.matInv` (definitions bundle `OAIQ019N047` of this split); `OAI.NuclearUltrapower.SOS.E` (definitions bundle `OAIQ019N049` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.SOS.ElementarySpectral.residual_value_native` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SOSGap.lean (declaration OAI.NuclearUltrapower.SOS.ElementarySpectral.value_inv)

import Mathlib
import Definitions.Def_OAIQ019N044

section

attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarPoly _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarPoly _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped ComplexOrder InnerProductSpace
namespace NuclearUltrapower.SOS.ElementarySpectral

section Algebra
variable {A : Type*} [CStarAlgebra A]

theorem value_inv (ρ : E →* unitary A) {n : ℕ} (a : Mat3) (ha : GoodWord n a) :
    value ρ (matInv a) = star (value ρ a) := by
  sorry

end Algebra

end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end
