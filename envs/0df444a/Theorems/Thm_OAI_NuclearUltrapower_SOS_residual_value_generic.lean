-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_SOS_residual_value_generic
-- name    : OAI.NuclearUltrapower.SOS.residual_value_generic
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T08:16:13.88199+00:00
-- url     : https://prove2.me/theorems/352c1502-cd1a-469e-a417-eba0a8da6acf
-- title:
--   OAI.NuclearUltrapower.SOS.residual_value_generic: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.SOS.residual_value_generic` of [lean/OAI/Analysis/NuclearUltrapower/IntegralCertificate.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/IntegralCertificate.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.SOS`):
--
--   ```lean
--   theorem residual_value_generic (f : Mat3 → A)
--       (hf : ∀ a ∈ delta.map Prod.fst, ∀ b ∈ delta.map Prod.fst,
--         f (matMul a b) = f a * f b)
--       (hg : ∀ a ∈ basis, ∀ b ∈ basis,
--         f (matMul (matInv a) b) = star (f a) * f b) :
--       eval f residual = (10000000000000 : ℤ) • (eval f delta * eval f delta) -
--         (1000000000000 : ℤ) • eval f delta - (10 : ℤ) • gramValue f
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.SOS.Mat3` and `OAI.NuclearUltrapower.SOS.eval` (definitions bundle `OAIQ019N000` of this split); `OAI.NuclearUltrapower.SOS.gramValue` (definitions bundle `OAIQ019N044` of this split); `OAI.NuclearUltrapower.SOS.basis`, `OAI.NuclearUltrapower.SOS.delta`, `OAI.NuclearUltrapower.SOS.matInv` and `OAI.NuclearUltrapower.SOS.matMul` (definitions bundle `OAIQ019N047` of this split); `OAI.NuclearUltrapower.SOS.residual` (definitions bundle `OAIQ019N049` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.SOS.ElementarySpectral.residual_value_native` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/IntegralCertificate.lean (declaration OAI.NuclearUltrapower.SOS.residual_value_generic)

import Mathlib
import Definitions.Def_OAIQ019N044

section

attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarPoly _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarPoly _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace NuclearUltrapower.SOS
section
variable {A : Type*} [Ring A] [StarRing A]
theorem residual_value_generic (f : Mat3 → A)
    (hf : ∀ a ∈ delta.map Prod.fst, ∀ b ∈ delta.map Prod.fst,
      f (matMul a b) = f a * f b)
    (hg : ∀ a ∈ basis, ∀ b ∈ basis,
      f (matMul (matInv a) b) = star (f a) * f b) :
    eval f residual = (10000000000000 : ℤ) • (eval f delta * eval f delta) -
      (1000000000000 : ℤ) • eval f delta - (10 : ℤ) • gramValue f := by
  sorry
end
end NuclearUltrapower.SOS
end
end

end OAI
end
