-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_primeGroupTail_coprime_mellin_height_power
-- name    : OAI.CubicFirstMoment.primeGroupTail_coprime_mellin_height_power
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:43:12.024434+00:00
-- url     : https://prove2.me/theorems/f447b350-3c8c-4e9e-9a93-d70684748110
-- title:
--   OAI.CubicFirstMoment.primeGroupTail_coprime_mellin_height_power: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.primeGroupTail_coprime_mellin_height_power` of [lean/OAI/NumberTheory/CubicMoment/Estimates/PrimeGroupTailCoprimeMass.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/PrimeGroupTailCoprimeMass.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open MeasureTheory`, `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem primeGroupTail_coprime_mellin_height_power
--       {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
--       (hHuxley : HuxleyAdditiveLargeSieve)
--       (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
--       (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (q : ℕ) :
--       ∃ K : ℝ, 0 < K ∧ ∀ (S H U : Finset Eisenstein) (β : Eisenstein → ℂ)
--         (Z : ℕ) (B T u ρ N : ℝ), 1 ≤ (Z:ℝ) → 1 ≤ B →
--         (Z:ℝ)^(1/50:ℝ) ≤ T → 0 ≤ ρ → 0 < N →
--         (∀ p ∈ U, primaryPrime p) →
--         (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
--         8*B ≤ (Z:ℝ)^(19/20:ℝ) → (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
--         (1+ρ)^q*dyadicHeightMean (fun t => ∫ s : ℝ,
--           ‖normDenominatorMellinCoefficient M hM V hV hV' ρ s‖*
--             twistedCoprimeMellinMass S H U β (fun a => norm a/N) (t+u) s) T ≤
--           K*(Z:ℝ)^(1-1/40000:ℝ)*B^(1/3:ℝ)*∑ b ∈ S, ‖β b‖^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.MontgomeryVaughanBound` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.dyadicHeightMean` (definitions bundle `OAIQ096A003` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve` and `OAI.CubicFirstMoment.normDenominatorMellinCoefficient` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.twistedCoprimeMellinMass` (definitions bundle `OAIQ096A020` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.norm`, `OAI.CubicFirstMoment.primary` and `OAI.CubicFirstMoment.primaryPrime` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI_CubicFirstMoment_primeGroupTail_common_row_height_power` and `OAI.CubicFirstMoment.primeGroupTail_common_sum_height_power` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/PrimeGroupTailCoprimeMass.lean (declaration OAI.CubicFirstMoment.primeGroupTail_coprime_mellin_height_power)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A020

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem primeGroupTail_coprime_mellin_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (q : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S H U : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (B T u ρ N : ℝ), 1 ≤ (Z:ℝ) → 1 ≤ B →
      (Z:ℝ)^(1/50:ℝ) ≤ T → 0 ≤ ρ → 0 < N →
      (∀ p ∈ U, primaryPrime p) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      8*B ≤ (Z:ℝ)^(19/20:ℝ) → (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      (1+ρ)^q*dyadicHeightMean (fun t => ∫ s : ℝ,
        ‖normDenominatorMellinCoefficient M hM V hV hV' ρ s‖*
          twistedCoprimeMellinMass S H U β (fun a => norm a/N) (t+u) s) T ≤
        K*(Z:ℝ)^(1-1/40000:ℝ)*B^(1/3:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  sorry

end CubicFirstMoment

end

end OAI
end
