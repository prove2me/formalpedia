-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_value_mul
-- name    : OAI.NuclearUltrapower.SOS.ElementarySpectral.value_mul
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T08:10:21.158208+00:00
-- url     : https://prove2.me/theorems/7b3db417-8632-4ce6-8f4c-111aff6f2fa0
-- title:
--   OAI.NuclearUltrapower.SOS.ElementarySpectral.value_mul: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.SOS.ElementarySpectral.value_mul` of [lean/OAI/Analysis/NuclearUltrapower/SOSGap.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SOSGap.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.SOS.ElementarySpectral`, with `open scoped ComplexOrder InnerProductSpace`):
--
--   ```lean
--   theorem value_mul (ρ : E →* unitary A) {n k : ℕ} (a b : Mat3)
--       (ha : GoodWord n a) (hb : GoodWord k b) :
--       value ρ (matMul a b) = value ρ a * value ρ b
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.SOS.Mat3` (definitions bundle `OAIQ019N000` of this split); `OAI.NuclearUltrapower.SOS.SL` (definitions bundle `OAIQ019N001` of this split); `OAI.NuclearUltrapower.SOS.GoodWord` and `OAI.NuclearUltrapower.SOS.ElementarySpectral.value` (definitions bundle `OAIQ019N044` of this split); `OAI.NuclearUltrapower.SOS.matMul` (definitions bundle `OAIQ019N047` of this split); `OAI.NuclearUltrapower.SOS.E` (definitions bundle `OAIQ019N049` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.SOS.ElementarySpectral.residual_value_native` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SOSGap.lean (declaration OAI.NuclearUltrapower.SOS.ElementarySpectral.value_mul)

import Mathlib
import Definitions.Def_OAIQ019N044

section

attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
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

theorem value_mul (ρ : E →* unitary A) {n k : ℕ} (a b : Mat3)
    (ha : GoodWord n a) (hb : GoodWord k b) :
    value ρ (matMul a b) = value ρ a * value ρ b := by
  sorry

end Algebra

end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end
