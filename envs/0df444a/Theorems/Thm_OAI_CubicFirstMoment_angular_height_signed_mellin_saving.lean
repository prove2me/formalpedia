-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_angular_height_signed_mellin_saving
-- name    : OAI.CubicFirstMoment.angular_height_signed_mellin_saving
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:17:09.418524+00:00
-- url     : https://prove2.me/theorems/8c611a35-e7f7-47bb-83f6-2bf579e3f2a0
-- title:
--   OAI.CubicFirstMoment.angular_height_signed_mellin_saving: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.angular_height_signed_mellin_saving` of [lean/OAI/NumberTheory/CubicMoment/Angular/AngularHeightSignedBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Angular/AngularHeightSignedBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open MeasureTheory`, `open scoped ContDiff`):
--
--   ```lean
--   theorem angular_height_signed_mellin_saving
--       (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
--       (hperiod : CubicSupplementaryPeriodicity)
--       {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
--       (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
--       (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
--       (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
--       (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ) (hV : HasCompactSupport V)
--       (hV' : ContDiff ℝ ∞ V) (k q : ℕ) :
--       ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
--       ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
--         LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
--         (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
--       ∃ (K L₀ : ℝ) (m : ℕ), 0 < K ∧
--         ∀ (r : γ) (X : ι → ℝ) (B : ℝ) (H : Finset Eisenstein)
--           (e : Eisenstein) (u T ρ : ℝ), L₀ ≤ L r →
--         (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
--         1 ≤ B → B ≤ (L r)^(1+η) →
--         (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
--         e ≠ 0 → norm e ≤ (L r)^σ → (1+Real.log (L r))^m ≤ T →
--         T ≤ (L r)^(7/20:ℝ) → |u| ≤ (L r)^(7/20:ℝ) → 0 ≤ ρ →
--         (1+ρ)^q*dyadicHeightMean (fun t => ∫ s : ℝ,
--           ‖normDenominatorMellinCoefficient M hM V hV hV' ρ s‖*
--           ((fullStructuredHeightMass R H 1 e ℓ (u+t) (W r) X (2*Real.pi*s)+
--             fullStructuredHeightMass R H 1 e ℓ (u+t) (W r) X (-(2*Real.pi*s)))/2)) T ≤
--           K*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.AngularGammaQuotientStripBound` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.GammaInverseFiniteOrder` and `OAI.CubicFirstMoment.LogarithmicWeightFamily` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.MontgomeryVaughanBound` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.dyadicHeightMean` (definitions bundle `OAIQ096A003` of this split); `OAI.CubicFirstMoment.CubicSupplementaryPeriodicity` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve`, `OAI.CubicFirstMoment.PrimitiveAngularHeckeInput` and `OAI.CubicFirstMoment.normDenominatorMellinCoefficient` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.fullStructuredHeightMass` (definitions bundle `OAIQ096A015` of this split); `OAI.CubicFirstMoment.Eisenstein` and `OAI.CubicFirstMoment.norm` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.angular_height_poisson_dyadic_saving` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Angular/AngularHeightSignedBound.lean (declaration OAI.CubicFirstMoment.angular_height_signed_mellin_saving)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A015

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_height_signed_mellin_saving
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (k q : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ (K L₀ : ℝ) (m : ℕ), 0 < K ∧
      ∀ (r : γ) (X : ι → ℝ) (B : ℝ) (H : Finset Eisenstein)
        (e : Eisenstein) (u T ρ : ℝ), L₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      1 ≤ B → B ≤ (L r)^(1+η) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      e ≠ 0 → norm e ≤ (L r)^σ → (1+Real.log (L r))^m ≤ T →
      T ≤ (L r)^(7/20:ℝ) → |u| ≤ (L r)^(7/20:ℝ) → 0 ≤ ρ →
      (1+ρ)^q*dyadicHeightMean (fun t => ∫ s : ℝ,
        ‖normDenominatorMellinCoefficient M hM V hV hV' ρ s‖*
        ((fullStructuredHeightMass R H 1 e ℓ (u+t) (W r) X (2*Real.pi*s)+
          fullStructuredHeightMass R H 1 e ℓ (u+t) (W r) X (-(2*Real.pi*s)))/2)) T ≤
        K*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  sorry

end CubicFirstMoment

end

end OAI
end
