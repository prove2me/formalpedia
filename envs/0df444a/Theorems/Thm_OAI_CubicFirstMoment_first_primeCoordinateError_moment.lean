-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_first_primeCoordinateError_moment
-- name    : OAI.CubicFirstMoment.first_primeCoordinateError_moment
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T04:41:17.904642+00:00
-- url     : https://prove2.me/theorems/97a1f451-7168-4bd6-aae9-181db6c5cf18
-- title:
--   OAI.CubicFirstMoment.first_primeCoordinateError_moment: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.first_primeCoordinateError_moment` of [lean/OAI/NumberTheory/CubicMoment/Estimates/PrimeCoordinateErrors.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/PrimeCoordinateErrors.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open scoped BigOperators`):
--
--   ```lean
--    theorem first_primeCoordinateError_moment {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) :
--       ∃ C : ℝ, 0 < C ∧ ∀ (q : ι → Eisenstein)
--         (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
--         (W : ι → ℝ → ℂ) (M X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ), 1 ≤ Y →
--         (∀ i, q i ≠ 0) → (∀ i, 0 ≤ M i) → (∀ i x, ‖W i x‖ ≤ M i) →
--         (∀ i x, x < 1 → W i x = 0) → (∀ i, (2*Y)^c < X i) →
--         (∀ x, ‖V x‖ ≤ 1) → ∀ P : Finset Eisenstein,
--         (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ (2*Y)^(1+c/256)) →
--         (∑ a ∈ P, ‖primeCoordinateError a 1 q η t W X V Y‖^2) ≤
--           C*(∏ i, M i)^2*(2*Y)^(7/3-c/32)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.primeCoordinateError` (definitions bundle `OAIQ096A019` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.Residues`, `OAI.CubicFirstMoment.modulus`, `OAI.CubicFirstMoment.norm` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.first_common_prime_exponents` and `OAI_CubicFirstMoment_full_exceptional_structured_moment` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/PrimeCoordinateErrors.lean (declaration OAI.CubicFirstMoment.first_primeCoordinateError_moment)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A019

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem first_primeCoordinateError_moment {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
      (W : ι → ℝ → ℂ) (M X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ), 1 ≤ Y →
      (∀ i, q i ≠ 0) → (∀ i, 0 ≤ M i) → (∀ i x, ‖W i x‖ ≤ M i) →
      (∀ i x, x < 1 → W i x = 0) → (∀ i, (2*Y)^c < X i) →
      (∀ x, ‖V x‖ ≤ 1) → ∀ P : Finset Eisenstein,
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ (2*Y)^(1+c/256)) →
      (∑ a ∈ P, ‖primeCoordinateError a 1 q η t W X V Y‖^2) ≤
        C*(∏ i, M i)^2*(2*Y)^(7/3-c/32) := by
  sorry

end CubicFirstMoment

end

end OAI
end
