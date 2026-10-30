-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_angular_two_prime_transition_centered
-- name    : OAI.CubicFirstMoment.angular_two_prime_transition_centered
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T04:22:50.546997+00:00
-- url     : https://prove2.me/theorems/05501e7c-026c-452e-a8e7-20230e55fd16
-- title:
--   OAI.CubicFirstMoment.angular_two_prime_transition_centered: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.angular_two_prime_transition_centered` of [lean/OAI/NumberTheory/CubicMoment/Angular/AngularTripleTransitionCentered.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Angular/AngularTripleTransitionCentered.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open scoped BigOperators ContDiff`, `open Filter`):
--
--   ```lean
--   theorem angular_two_prime_transition_centered {γ ι : Type*} [Fintype ι] [DecidableEq ι]
--       (hcard : Fintype.card ι = 2) (hpnt : PrimaryPrimePNT)
--       (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0) (hpub : PrimitiveAngularHeckeInput)
--       (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
--       {C c : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (hc : 0 < c)
--       (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
--       (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
--       (L : γ → ℝ) (W : γ → ℝ → ℂ) (hL : ∀ r, 1 ≤ L r)
--       (hW : UniformLogWeights W) (hlo : ∀ r x, x < 1 → W r x = 0)
--       (hhi : ∀ r x, 2 < x → W r x = 0) (hW1 : ∀ r x, ‖W r x‖ ≤ 1) (U : ℕ) :
--       ∃ η K T₀ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
--         ∀ (r : γ) (A u : ℝ) (WA : ι → ℝ → ℂ) (XA : ι → ℝ),
--         T₀ ≤ L r → (2*L r)^(1/2:ℝ) < L r →
--         (L r)^(1-η/4) ≤ A → A ≤ (L r)^2 → |u| ≤ (1+Real.log (L r))^U →
--         (∏ i, XA i) = A → (∀ i, (L r)^c ≤ XA i) →
--         (∀ i x, x < 1 → WA i x = 0) → (∀ i x, 2 < x → WA i x = 0) →
--         (∀ i x, ‖WA i x‖ ≤ 1) →
--         ‖centeredProductPolynomial (fullSquarefreePrimeSupport 2 WA XA 1)
--           (fullSquarefreePrimeSupport 2 (fun _ : Unit => W r) (fun _ => L r) 1)
--           (fullPrimeCoefficient 2 WA XA)
--           (fullPrimeCoefficient 2 (fun _ : Unit => W r) (fun _ => L r)) ℓ u‖ ≤
--           K*A^(5/6:ℝ)*(L r)^(5/6:ℝ)/(1+Real.log (L r))^(3/2:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.AngularGammaQuotientStripBound` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.GammaInverseFiniteOrder` and `OAI.CubicFirstMoment.UniformLogWeights` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.MontgomeryVaughanBound` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.AngularKummerPrimeExplicitEstimate` and `OAI.CubicFirstMoment.CubicSupplementaryPeriodicity` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve`, `OAI.CubicFirstMoment.PrimaryPrimePNT`, `OAI.CubicFirstMoment.PrimitiveAngularHeckeInput` and `OAI.CubicFirstMoment.fullPrimeCoefficient` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.centeredProductPolynomial` (definitions bundle `OAIQ096A008` of this split); `OAI.CubicFirstMoment.fullSquarefreePrimeSupport` (definitions bundle `OAIQ096A011` of this split); `OAI.CubicFirstMoment.Eisenstein` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.angular_large_tuple_triple_transition_smoothed` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Angular/AngularTripleTransitionCentered.lean (declaration OAI.CubicFirstMoment.angular_two_prime_transition_centered)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A011

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_two_prime_transition_centered {γ ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 2) (hpnt : PrimaryPrimePNT)
    (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0) (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C c : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (hc : 0 < c)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (L : γ → ℝ) (W : γ → ℝ → ℂ) (hL : ∀ r, 1 ≤ L r)
    (hW : UniformLogWeights W) (hlo : ∀ r x, x < 1 → W r x = 0)
    (hhi : ∀ r x, 2 < x → W r x = 0) (hW1 : ∀ r x, ‖W r x‖ ≤ 1) (U : ℕ) :
    ∃ η K T₀ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ (r : γ) (A u : ℝ) (WA : ι → ℝ → ℂ) (XA : ι → ℝ),
      T₀ ≤ L r → (2*L r)^(1/2:ℝ) < L r →
      (L r)^(1-η/4) ≤ A → A ≤ (L r)^2 → |u| ≤ (1+Real.log (L r))^U →
      (∏ i, XA i) = A → (∀ i, (L r)^c ≤ XA i) →
      (∀ i x, x < 1 → WA i x = 0) → (∀ i x, 2 < x → WA i x = 0) →
      (∀ i x, ‖WA i x‖ ≤ 1) →
      ‖centeredProductPolynomial (fullSquarefreePrimeSupport 2 WA XA 1)
        (fullSquarefreePrimeSupport 2 (fun _ : Unit => W r) (fun _ => L r) 1)
        (fullPrimeCoefficient 2 WA XA)
        (fullPrimeCoefficient 2 (fun _ : Unit => W r) (fun _ => L r)) ℓ u‖ ≤
        K*A^(5/6:ℝ)*(L r)^(5/6:ℝ)/(1+Real.log (L r))^(3/2:ℝ) := by
  sorry

end CubicFirstMoment

end

end OAI
end
