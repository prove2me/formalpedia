-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_primitive_angular_prime_ideal_estimate
-- name    : OAI.CubicFirstMoment.primitive_angular_prime_ideal_estimate
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T04:27:30.745266+00:00
-- url     : https://prove2.me/theorems/abbefd9e-3fb0-40bd-984f-298b5cd884a9
-- title:
--   OAI.CubicFirstMoment.primitive_angular_prime_ideal_estimate: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.primitive_angular_prime_ideal_estimate` of [lean/OAI/NumberTheory/CubicMoment/Estimates/PrimitiveAngularPrimeEstimate.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/PrimitiveAngularPrimeEstimate.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`):
--
--   ```lean
--   theorem primitive_angular_prime_ideal_estimate (hpub : PrimitiveAngularHeckeInput) :
--       ∃ B c X0 : ℝ, 0 < B ∧ 0 < c ∧ c ≤ 1/4 ∧ 1 < X0 ∧
--       ∀ (q : Eisenstein), q ≠ 0 → ∀ χ : MulChar (Residues q) ℂ,
--       PrimitiveResidueCharacter q χ → ∀ ℓ : ℤ, ℓ ≠ 0 → AngularUnitCompatible q χ ℓ →
--       ∀ Q : ℝ, 1 ≤ Q → 2*norm q*(1+norm q) ≤ Q → |(ℓ:ℝ)|+7 ≤ Q →
--       ∀ X : ℝ, X0 ≤ X → ‖idealPrimeChebyshev (angularResidueIdealChar q χ ℓ) X‖ ≤
--         B*primeCancellationWeight c Q X
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.primeCancellationWeight` (definitions bundle `OAIQ096A003` of this split); `OAI.CubicFirstMoment.AngularUnitCompatible` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.PrimitiveAngularHeckeInput`, `OAI.CubicFirstMoment.PrimitiveResidueCharacter` and `OAI.CubicFirstMoment.angularResidueIdealChar` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.idealPrimeChebyshev` (definitions bundle `OAIQ096A015` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.Residues`, `OAI.CubicFirstMoment.modulus` and `OAI.CubicFirstMoment.norm` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI_CubicFirstMoment_angularKummerPrimeExplicitEstimate_of_primitive`, `OAI.CubicFirstMoment.cubicTheta_primeProductLowHeight_isLittleO` and `OAI.CubicFirstMoment.patterson_angularCancellation` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/PrimitiveAngularPrimeEstimate.lean (declaration OAI.CubicFirstMoment.primitive_angular_prime_ideal_estimate)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A015

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CubicFirstMoment

theorem primitive_angular_prime_ideal_estimate (hpub : PrimitiveAngularHeckeInput) :
    ∃ B c X0 : ℝ, 0 < B ∧ 0 < c ∧ c ≤ 1/4 ∧ 1 < X0 ∧
    ∀ (q : Eisenstein), q ≠ 0 → ∀ χ : MulChar (Residues q) ℂ,
    PrimitiveResidueCharacter q χ → ∀ ℓ : ℤ, ℓ ≠ 0 → AngularUnitCompatible q χ ℓ →
    ∀ Q : ℝ, 1 ≤ Q → 2*norm q*(1+norm q) ≤ Q → |(ℓ:ℝ)|+7 ≤ Q →
    ∀ X : ℝ, X0 ≤ X → ‖idealPrimeChebyshev (angularResidueIdealChar q χ ℓ) X‖ ≤
      B*primeCancellationWeight c Q X := by
  sorry

end CubicFirstMoment

end

end OAI
end
