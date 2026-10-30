-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_angular_exceptional_residual_moment
-- name    : OAI.CubicFirstMoment.angular_exceptional_residual_moment
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T04:14:42.560843+00:00
-- url     : https://prove2.me/theorems/de26405a-97e7-4d12-b656-a44c15b3d313
-- title:
--   OAI.CubicFirstMoment.angular_exceptional_residual_moment: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.angular_exceptional_residual_moment` of [lean/OAI/NumberTheory/CubicMoment/Angular/AngularExceptionalResidualMoment.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Angular/AngularExceptionalResidualMoment.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem angular_exceptional_residual_moment (hpub : PrimitiveAngularHeckeInput)
--       (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
--       {c R : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
--       (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
--       (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
--       ∃ δ ν : ℝ, 0 < δ ∧ 0 < ν ∧
--       ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
--         LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
--         (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
--       ∃ T : ℝ, ∀ (r : γ) (X : ι → ℝ) (v e : Eisenstein) (u p q : ℝ)
--         (Ram J H : Finset Eisenstein) (P : Finset (Eisenstein × Eisenstein)), T ≤ L r →
--         (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
--         v ≠ 0 → e ≠ 0 → norm v ≤ (L r)^δ → norm e ≤ (L r)^δ →
--         1+|u| ≤ (L r)^(9/25:ℝ) →
--         (∀ a ∈ Ram, a ≠ 0 ∧ norm a ≤ (L r)^δ) →
--         (∀ j ∈ J, j ≠ 0 ∧ norm j ≤ (L r)^δ) →
--         (∀ z ∈ P, gramDyad ((L r)^p) z.1 ∧ gramDyad ((L r)^q) z.2 ∧ IsCoprime z.1 z.2) →
--         ((|p-1| ≤ δ ∧ 0 ≤ q ∧ q ≤ δ) ∨ (|p-1/3| ≤ δ ∧ |q-1/3| ≤ δ)) →
--         H ⊆ coprimeResidualSupport Ram J P →
--         (∑ h ∈ H, ‖fullStructuredAngularPrimeSum ℓ R h 1 v e u (W r) X‖^2) ≤
--           (Ram.card:ℝ)*J.card*(L r)^2*((L r)^p*((L r)^q)^2)^(1/3:ℝ)*(L r)^(-ν)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.AngularGammaQuotientStripBound` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.GammaInverseFiniteOrder` and `OAI.CubicFirstMoment.LogarithmicWeightFamily` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.CubicSupplementaryPeriodicity` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.gramDyad` (definitions bundle `OAIQ096A005` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve` and `OAI.CubicFirstMoment.PrimitiveAngularHeckeInput` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.coprimeResidualSupport` (definitions bundle `OAIQ096A008` of this split); `OAI.CubicFirstMoment.fullStructuredAngularPrimeSum` (definitions bundle `OAIQ096A015` of this split); `OAI.CubicFirstMoment.Eisenstein` and `OAI.CubicFirstMoment.norm` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.angular_height_signed_mellin_saving` and `OAI.CubicFirstMoment.angular_large_core_mellin_integral_saving` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Angular/AngularExceptionalResidualMoment.lean (declaration OAI.CubicFirstMoment.angular_exceptional_residual_moment)

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
open scoped BigOperators
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_exceptional_residual_moment (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {c R : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ δ ν : ℝ, 0 < δ ∧ 0 < ν ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ T : ℝ, ∀ (r : γ) (X : ι → ℝ) (v e : Eisenstein) (u p q : ℝ)
      (Ram J H : Finset Eisenstein) (P : Finset (Eisenstein × Eisenstein)), T ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      v ≠ 0 → e ≠ 0 → norm v ≤ (L r)^δ → norm e ≤ (L r)^δ →
      1+|u| ≤ (L r)^(9/25:ℝ) →
      (∀ a ∈ Ram, a ≠ 0 ∧ norm a ≤ (L r)^δ) →
      (∀ j ∈ J, j ≠ 0 ∧ norm j ≤ (L r)^δ) →
      (∀ z ∈ P, gramDyad ((L r)^p) z.1 ∧ gramDyad ((L r)^q) z.2 ∧ IsCoprime z.1 z.2) →
      ((|p-1| ≤ δ ∧ 0 ≤ q ∧ q ≤ δ) ∨ (|p-1/3| ≤ δ ∧ |q-1/3| ≤ δ)) →
      H ⊆ coprimeResidualSupport Ram J P →
      (∑ h ∈ H, ‖fullStructuredAngularPrimeSum ℓ R h 1 v e u (W r) X‖^2) ≤
        (Ram.card:ℝ)*J.card*(L r)^2*((L r)^p*((L r)^q)^2)^(1/3:ℝ)*(L r)^(-ν) := by
  sorry

end CubicFirstMoment

end

end OAI
end
