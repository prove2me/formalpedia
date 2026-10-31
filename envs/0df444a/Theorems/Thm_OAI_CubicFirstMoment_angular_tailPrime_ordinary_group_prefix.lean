-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_angular_tailPrime_ordinary_group_prefix
-- name    : OAI.CubicFirstMoment.angular_tailPrime_ordinary_group_prefix
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:35:23.014441+00:00
-- url     : https://prove2.me/theorems/528871ef-92d5-4b99-8907-02e36e0cb234
-- title:
--   OAI.CubicFirstMoment.angular_tailPrime_ordinary_group_prefix: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.angular_tailPrime_ordinary_group_prefix` of [lean/OAI/NumberTheory/CubicMoment/Angular/AngularTailPrimeOrdinaryBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Angular/AngularTailPrimeOrdinaryBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Filter`, `open scoped BigOperators`):
--
--   ```lean
--   theorem angular_tailPrime_ordinary_group_prefix {i j : ℕ} (s : Finset (Fin i ⊕ Fin j))
--       (hpnt : PrimaryPrimePNT) (hpub : PrimitiveAngularHeckeInput)
--       (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
--       {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
--       (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
--       (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
--       (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) (n : ℕ) :
--       ∃ (Ct : ℕ) (K : ℝ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
--         ∀ (z : largeTupleBoxIndex i j) (H T : ℝ), z.1.1 = X →
--         let B := largeTupleGroupLength s z
--         let A := largeTupleGroupLength (Finset.univ\s) z
--         ((1/2:ℝ)^(1/3:ℝ)/2^(i+j))*X^(1/3:ℝ) ≤ B → B^2 ≤ 3*X →
--         X/(2*2^(i+j)) ≤ A*B → A*B ≤ 3*X →
--         (∀ a : s, (2*B)^(ξ/2) < largeTupleNormScale z.1.2 a) →
--         (1+Real.log X)^Ct ≤ T → 1 ≤ H → H ≤ X^(1/6+1/3000:ℝ) →
--         ‖∑ v ∈ Finset.range (heightWindowCount H T),
--           if T*(3/2:ℝ)^v ≤ X^(1/100:ℝ) then
--             productGaussWindow (largeTupleSelectedSupport ξ z.1.1 z.1.2 s)
--               (largeTupleOtherSupport ξ z.1.1 z.1.2 s)
--               (largeTupleSelectedCoefficient ξ z.1.1 z.1.2 s)
--               (largeTupleOtherCoefficient ξ z.1.1 z.1.2 s)
--               ℓ primeProductEnvelope H (T*(3/2:ℝ)^v) z.1.1 else 0‖ ≤
--           K*X^(5/6:ℝ)/(1+Real.log X)^n
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.AngularGammaQuotientStripBound` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.GammaInverseFiniteOrder` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.MontgomeryVaughanBound`, `OAI.CubicFirstMoment.heightWindowCount`, `OAI.CubicFirstMoment.largeTupleNormScale` and `OAI.CubicFirstMoment.primeProductEnvelope` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.CubicSupplementaryPeriodicity` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.largeTupleBoxIndex` and `OAI.CubicFirstMoment.largeTupleGroupLength` (definitions bundle `OAIQ096A006` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve`, `OAI.CubicFirstMoment.PrimaryPrimePNT` and `OAI.CubicFirstMoment.PrimitiveAngularHeckeInput` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.largeTupleOtherCoefficient` and `OAI.CubicFirstMoment.largeTupleSelectedCoefficient` (definitions bundle `OAIQ096A015` of this split); `OAI.CubicFirstMoment.largeTupleOtherSupport`, `OAI.CubicFirstMoment.largeTupleSelectedSupport` and `OAI.CubicFirstMoment.productGaussWindow` (definitions bundle `OAIQ096A019` of this split).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.primeProductGaussTail_angular_isLittleO_proved` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Angular/AngularTailPrimeOrdinaryBounds.lean (declaration OAI.CubicFirstMoment.angular_tailPrime_ordinary_group_prefix)

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
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_tailPrime_ordinary_group_prefix {i j : ℕ} (s : Finset (Fin i ⊕ Fin j))
    (hpnt : PrimaryPrimePNT) (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) (n : ℕ) :
    ∃ (Ct : ℕ) (K : ℝ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (z : largeTupleBoxIndex i j) (H T : ℝ), z.1.1 = X →
      let B := largeTupleGroupLength s z
      let A := largeTupleGroupLength (Finset.univ\s) z
      ((1/2:ℝ)^(1/3:ℝ)/2^(i+j))*X^(1/3:ℝ) ≤ B → B^2 ≤ 3*X →
      X/(2*2^(i+j)) ≤ A*B → A*B ≤ 3*X →
      (∀ a : s, (2*B)^(ξ/2) < largeTupleNormScale z.1.2 a) →
      (1+Real.log X)^Ct ≤ T → 1 ≤ H → H ≤ X^(1/6+1/3000:ℝ) →
      ‖∑ v ∈ Finset.range (heightWindowCount H T),
        if T*(3/2:ℝ)^v ≤ X^(1/100:ℝ) then
          productGaussWindow (largeTupleSelectedSupport ξ z.1.1 z.1.2 s)
            (largeTupleOtherSupport ξ z.1.1 z.1.2 s)
            (largeTupleSelectedCoefficient ξ z.1.1 z.1.2 s)
            (largeTupleOtherCoefficient ξ z.1.1 z.1.2 s)
            ℓ primeProductEnvelope H (T*(3/2:ℝ)^v) z.1.1 else 0‖ ≤
        K*X^(5/6:ℝ)/(1+Real.log X)^n := by
  sorry

end CubicFirstMoment

end

end OAI
end
