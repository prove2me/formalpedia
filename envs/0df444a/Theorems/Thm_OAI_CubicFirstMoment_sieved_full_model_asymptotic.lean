-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_sieved_full_model_asymptotic
-- name    : OAI.CubicFirstMoment.sieved_full_model_asymptotic
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:28:34.17019+00:00
-- url     : https://prove2.me/theorems/54c73693-aa8c-4fea-b5e4-9a4f7b4b2de3
-- title:
--   OAI.CubicFirstMoment.sieved_full_model_asymptotic: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.sieved_full_model_asymptotic` of [lean/OAI/NumberTheory/CubicMoment/Estimates/SievedFullModel.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/SievedFullModel.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open scoped BigOperators ContDiff`, `open Filter`):
--
--   ```lean
--   theorem sieved_full_model_asymptotic (hSW : KummerPrimeSiegelWalfisz)
--       (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
--       (hperiod : CubicSupplementaryPeriodicity)
--       {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
--       (hc : 0 < c) (hc1 : c ≤ 1) (hR : 1 ≤ R)
--       (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
--       (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
--       (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k U b : ℕ) :
--       ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
--       ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
--         LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
--         (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
--       ∃ (G : ℕ) (K T₀ : ℝ), 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (A : ℝ)
--         (e : Eisenstein) (u : ℝ), T₀ ≤ L r →
--         (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
--         (L r)^(1-η/16) ≤ A → A ≤ (L r)^2/(1+Real.log (L r))^G →
--         e ≠ 0 → norm e ≤ (L r)^σ → |u| ≤ (1+Real.log (L r))^U →
--         ‖sievedDispersionVariance (squarefreeDivisorTruncation ((1+Real.log (L r))^b))
--             (fullSquarefreePrimeSupport R (W r) X e) (fullPrimeCoefficient R (W r) X) u V A-
--           (finiteSieveDensity (squarefreeDivisorTruncation ((1+Real.log (L r))^b)):ℂ)*
--             cubeModelTerm (fullSquarefreePrimeSupport R (W r) X e)
--               (fullPrimeCoefficient R (W r) X) u V A‖ ≤
--           K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.GammaInverseFiniteOrder`, `OAI.CubicFirstMoment.GammaQuotientStripBound` and `OAI.CubicFirstMoment.LogarithmicWeightFamily` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.MontgomeryVaughanBound` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.CubicSupplementaryPeriodicity` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.squarefreeDivisorTruncation` (definitions bundle `OAIQ096A006` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve`, `OAI.CubicFirstMoment.KummerPrimeSiegelWalfisz`, `OAI.CubicFirstMoment.PrimitiveResidueHeckeInput` and `OAI.CubicFirstMoment.fullPrimeCoefficient` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.cubeModelTerm` (definitions bundle `OAIQ096A008` of this split); `OAI.CubicFirstMoment.finiteSieveDensity` and `OAI.CubicFirstMoment.sievedDispersionVariance` (definitions bundle `OAIQ096A010` of this split); `OAI.CubicFirstMoment.fullSquarefreePrimeSupport` (definitions bundle `OAIQ096A011` of this split); `OAI.CubicFirstMoment.Eisenstein` and `OAI.CubicFirstMoment.norm` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.full_prime_centered_product_bilinear_actual` and `OAI.CubicFirstMoment.semiprime_block_log_saving_actual` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/SievedFullModel.lean (declaration OAI.CubicFirstMoment.sieved_full_model_asymptotic)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A010
import Definitions.Def_OAIQ096A011

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open Filter
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem sieved_full_model_asymptotic (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc1 : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k U b : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ (G : ℕ) (K T₀ : ℝ), 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (A : ℝ)
      (e : Eisenstein) (u : ℝ), T₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      (L r)^(1-η/16) ≤ A → A ≤ (L r)^2/(1+Real.log (L r))^G →
      e ≠ 0 → norm e ≤ (L r)^σ → |u| ≤ (1+Real.log (L r))^U →
      ‖sievedDispersionVariance (squarefreeDivisorTruncation ((1+Real.log (L r))^b))
          (fullSquarefreePrimeSupport R (W r) X e) (fullPrimeCoefficient R (W r) X) u V A-
        (finiteSieveDensity (squarefreeDivisorTruncation ((1+Real.log (L r))^b)):ℂ)*
          cubeModelTerm (fullSquarefreePrimeSupport R (W r) X e)
            (fullPrimeCoefficient R (W r) X) u V A‖ ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  sorry

end CubicFirstMoment

end

end OAI
end
