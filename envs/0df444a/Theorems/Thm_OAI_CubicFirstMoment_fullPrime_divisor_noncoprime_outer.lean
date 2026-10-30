-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_fullPrime_divisor_noncoprime_outer
-- name    : OAI.CubicFirstMoment.fullPrime_divisor_noncoprime_outer
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T04:25:38.115992+00:00
-- url     : https://prove2.me/theorems/5c9d6ff3-52b7-48a4-8e51-6bd164af3aed
-- title:
--   OAI.CubicFirstMoment.fullPrime_divisor_noncoprime_outer: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.fullPrime_divisor_noncoprime_outer` of [lean/OAI/NumberTheory/CubicMoment/Estimates/CommonRemainderBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/CommonRemainderBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open scoped BigOperators ContDiff`):
--
--   ```lean
--    theorem fullPrime_divisor_noncoprime_outer {ι : Type*} [Fintype ι] [DecidableEq ι]
--       {ε R : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 1 ≤ R)
--       (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
--       ∃ C : ℝ, 0 < C ∧ ∀ (W : ι → ℝ → ℂ) (X : ι → ℝ) (L D A : ℝ)
--         (e d : Eisenstein) (β : Eisenstein → ℂ) (u : ℝ),
--         (∀ i, 0 < X i) → (∏ i, X i) = L → 1 ≤ L → 1 ≤ D → 0 < A → primary d →
--         (∀ i x, x < 1 → W i x = 0) → (∀ i x, R < x → W i x = 0) →
--         (∀ i, D < X i) →
--         ‖divisorDispersionVariance d (fullSquarefreePrimeSupport R W X e) β u V A-
--           divisorCoprimeDispersionGram d (fullSquarefreePrimeSupport R W X e) β u V A‖ ≤
--         commonOuterCost V C ε (R^Fintype.card ι) (norm d) A L D*
--           (2:ℝ)^(3*Fintype.card ι)*
--             ∑ a ∈ fullSquarefreePrimeSupport R W X e, ‖β a‖^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.commonOuterCost` (definitions bundle `OAIQ096A005` of this split); `OAI.CubicFirstMoment.divisorDispersionVariance` (definitions bundle `OAIQ096A010` of this split); `OAI.CubicFirstMoment.fullSquarefreePrimeSupport` (definitions bundle `OAIQ096A011` of this split); `OAI.CubicFirstMoment.divisorCoprimeDispersionGram` (definitions bundle `OAIQ096A015` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.norm` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI_CubicFirstMoment_angular_divisor_full_model_asymptotic`, `OAI.CubicFirstMoment.angular_full_prime_centered_smoothed_bilinear_actual`, `OAI_CubicFirstMoment_angular_full_prime_product_height_bilinear`, `OAI.CubicFirstMoment.angular_sieved_full_model_asymptotic`, `OAI.CubicFirstMoment.angular_tailPrime_hecke_group`, `OAI.CubicFirstMoment.angular_tailPrime_hecke_window`, `OAI.CubicFirstMoment.full_prime_product_height_bilinear`, `OAI.CubicFirstMoment.semiprimeGaussTail_angular_hecke_window`, `OAI.CubicFirstMoment.semiprime_gauss_height_log_saving`, `OAI.CubicFirstMoment.sieved_full_model_asymptotic` and `OAI_CubicFirstMoment_sieved_squarefree_model_asymptotic` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/CommonRemainderBound.lean (declaration OAI.CubicFirstMoment.fullPrime_divisor_noncoprime_outer)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A011
import Definitions.Def_OAIQ096A015

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

 theorem fullPrime_divisor_noncoprime_outer {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ε R : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 1 ≤ R)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ι → ℝ → ℂ) (X : ι → ℝ) (L D A : ℝ)
      (e d : Eisenstein) (β : Eisenstein → ℂ) (u : ℝ),
      (∀ i, 0 < X i) → (∏ i, X i) = L → 1 ≤ L → 1 ≤ D → 0 < A → primary d →
      (∀ i x, x < 1 → W i x = 0) → (∀ i x, R < x → W i x = 0) →
      (∀ i, D < X i) →
      ‖divisorDispersionVariance d (fullSquarefreePrimeSupport R W X e) β u V A-
        divisorCoprimeDispersionGram d (fullSquarefreePrimeSupport R W X e) β u V A‖ ≤
      commonOuterCost V C ε (R^Fintype.card ι) (norm d) A L D*
        (2:ℝ)^(3*Fintype.card ι)*
          ∑ a ∈ fullSquarefreePrimeSupport R W X e, ‖β a‖^2 := by
  sorry

end CubicFirstMoment

end

end OAI
end
