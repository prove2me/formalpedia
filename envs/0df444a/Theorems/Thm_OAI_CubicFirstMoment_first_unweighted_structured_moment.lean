-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_first_unweighted_structured_moment
-- name    : OAI.CubicFirstMoment.first_unweighted_structured_moment
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T04:49:51.970913+00:00
-- url     : https://prove2.me/theorems/a52cc8cc-b5fe-4b69-b32b-2d6fa912a941
-- title:
--   OAI.CubicFirstMoment.first_unweighted_structured_moment: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.first_unweighted_structured_moment` of [lean/OAI/NumberTheory/CubicMoment/Estimates/FirstUnweightedStructuredMoment.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/FirstUnweightedStructuredMoment.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Set Filter`, `open scoped ContDiff BigOperators`):
--
--   ```lean
--   theorem first_unweighted_structured_moment (hpub : PrimitiveResidueHeckeInput)
--       (hperiod : CubicSupplementaryPeriodicity) {c R : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1)
--       (hR : 1 ≤ R) (J : ℕ) (hJ : 2*R^(Fintype.card ι) ≤ (4/3:ℝ)^J)
--       (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
--       (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
--       ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧
--         ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
--         LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
--         (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) → ∃ T : ℝ,
--         ∀ (r : γ) (N : ℝ) (X : ι → ℝ) (v e : Eisenstein) (u : ℝ) (P Q : Finset Eisenstein),
--         T ≤ L r → (L r)^(1-δ) ≤ N → N ≤ (L r)^(1+δ) →
--         (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) → (∀ i, X i ≤ L r) → v ≠ 0 → e ≠ 0 →
--         norm v ≤ (L r)^δ → norm e ≤ (L r)^δ → |u| ≤ (L r)^(9/25:ℝ) →
--         (∀ a ∈ P, gramDyad N a) → (∀ b ∈ Q, primary b ∧ norm b ≤ (L r)^δ) →
--         (∑ b ∈ Q, ∑ a ∈ P,
--           ‖structuredPrimeSum a b v e u (W r) X (((4/3:ℝ)^J/2)*L r)‖^2) ≤ (L r)^(7/3-ε)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.GammaInverseFiniteOrder`, `OAI.CubicFirstMoment.GammaQuotientStripBound` and `OAI.CubicFirstMoment.LogarithmicWeightFamily` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.CubicSupplementaryPeriodicity` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.gramDyad` (definitions bundle `OAIQ096A005` of this split); `OAI.CubicFirstMoment.PrimitiveResidueHeckeInput` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.structuredPrimeSum` (definitions bundle `OAIQ096A023` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.norm` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.uniform_core_block_polynomial_height` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/FirstUnweightedStructuredMoment.lean (declaration OAI.CubicFirstMoment.first_unweighted_structured_moment)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A023

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem first_unweighted_structured_moment (hpub : PrimitiveResidueHeckeInput)
    (hperiod : CubicSupplementaryPeriodicity) {c R : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1)
    (hR : 1 ≤ R) (J : ℕ) (hJ : 2*R^(Fintype.card ι) ≤ (4/3:ℝ)^J)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) → ∃ T : ℝ,
      ∀ (r : γ) (N : ℝ) (X : ι → ℝ) (v e : Eisenstein) (u : ℝ) (P Q : Finset Eisenstein),
      T ≤ L r → (L r)^(1-δ) ≤ N → N ≤ (L r)^(1+δ) →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) → (∀ i, X i ≤ L r) → v ≠ 0 → e ≠ 0 →
      norm v ≤ (L r)^δ → norm e ≤ (L r)^δ → |u| ≤ (L r)^(9/25:ℝ) →
      (∀ a ∈ P, gramDyad N a) → (∀ b ∈ Q, primary b ∧ norm b ≤ (L r)^δ) →
      (∑ b ∈ Q, ∑ a ∈ P,
        ‖structuredPrimeSum a b v e u (W r) X (((4/3:ℝ)^J/2)*L r)‖^2) ≤ (L r)^(7/3-ε) := by
  sorry

end CubicFirstMoment

end

end OAI
end
