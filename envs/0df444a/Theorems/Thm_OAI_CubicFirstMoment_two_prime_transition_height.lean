-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_two_prime_transition_height
-- name    : OAI.CubicFirstMoment.two_prime_transition_height
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:47:51.472883+00:00
-- url     : https://prove2.me/theorems/c4892fe3-4fff-4171-a96f-38a55286d853
-- title:
--   OAI.CubicFirstMoment.two_prime_transition_height: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.two_prime_transition_height` of [lean/OAI/NumberTheory/CubicMoment/Estimates/TripleTransitionHeight.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/TripleTransitionHeight.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem two_prime_transition_height {γ ι : Type*} [Fintype ι] [DecidableEq ι]
--       (hcard : Fintype.card ι = 2)
--       (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
--       (hperiod : CubicSupplementaryPeriodicity)
--       {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
--       (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
--       (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
--       (L : γ → ℝ) (W : γ → ℝ → ℂ) (hL : ∀ r, 1 ≤ L r)
--       (hW : UniformLogWeights W) (hlo : ∀ r x, x < 1 → W r x = 0)
--       (hhi : ∀ r x, 2 < x → W r x = 0) (hW1 : ∀ r x, ‖W r x‖ ≤ 1) :
--       ∃ (η K B₀ : ℝ) (m : ℕ), 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
--         ∀ (r : γ) (A u T : ℝ) (WA : ι → ℝ → ℂ) (XA : ι → ℝ),
--         B₀ ≤ L r → (2*L r)^(1/2:ℝ) < L r →
--         (L r)^(1-η/4) ≤ A → A ≤ (L r)^2 →
--         (1+Real.log (L r))^m ≤ T → T ≤ (L r)^(7/20:ℝ) → |u| ≤ (L r)^(7/20:ℝ) →
--         (∏ i, XA i) = A → (∀ i, 0 < XA i) →
--         (∀ i x, x < 1 → WA i x = 0) → (∀ i x, 2 < x → WA i x = 0) →
--         (∀ i x, ‖WA i x‖ ≤ 1) →
--         dyadicHeightMean (fun t =>
--           ‖fullPrimeProductGauss 2 WA (fun _ : Unit => W r) XA (fun _ => L r) (u+t)‖) T ≤
--           K*A^(5/6:ℝ)*(L r)^(5/6:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.GammaInverseFiniteOrder`, `OAI.CubicFirstMoment.GammaQuotientStripBound` and `OAI.CubicFirstMoment.UniformLogWeights` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.MontgomeryVaughanBound` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.dyadicHeightMean` (definitions bundle `OAIQ096A003` of this split); `OAI.CubicFirstMoment.CubicSupplementaryPeriodicity` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve` and `OAI.CubicFirstMoment.PrimitiveResidueHeckeInput` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.fullPrimeProductGauss` (definitions bundle `OAIQ096A019` of this split).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.largePrimeTupleSelectedFlatHighSum_isLittleO` and `OAI_CubicFirstMoment_large_tuple_triple_transition_smoothed` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/TripleTransitionHeight.lean (declaration OAI.CubicFirstMoment.two_prime_transition_height)

import Mathlib
import Definitions.Def_OAIQ096A019

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem two_prime_transition_height {γ ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 2)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (L : γ → ℝ) (W : γ → ℝ → ℂ) (hL : ∀ r, 1 ≤ L r)
    (hW : UniformLogWeights W) (hlo : ∀ r x, x < 1 → W r x = 0)
    (hhi : ∀ r x, 2 < x → W r x = 0) (hW1 : ∀ r x, ‖W r x‖ ≤ 1) :
    ∃ (η K B₀ : ℝ) (m : ℕ), 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ (r : γ) (A u T : ℝ) (WA : ι → ℝ → ℂ) (XA : ι → ℝ),
      B₀ ≤ L r → (2*L r)^(1/2:ℝ) < L r →
      (L r)^(1-η/4) ≤ A → A ≤ (L r)^2 →
      (1+Real.log (L r))^m ≤ T → T ≤ (L r)^(7/20:ℝ) → |u| ≤ (L r)^(7/20:ℝ) →
      (∏ i, XA i) = A → (∀ i, 0 < XA i) →
      (∀ i x, x < 1 → WA i x = 0) → (∀ i x, 2 < x → WA i x = 0) →
      (∀ i x, ‖WA i x‖ ≤ 1) →
      dyadicHeightMean (fun t =>
        ‖fullPrimeProductGauss 2 WA (fun _ : Unit => W r) XA (fun _ => L r) (u+t)‖) T ≤
        K*A^(5/6:ℝ)*(L r)^(5/6:ℝ) := by
  sorry

end CubicFirstMoment

end

end OAI
end
