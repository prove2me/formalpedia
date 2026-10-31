-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_tailPrime_low_group
-- name    : OAI.CubicFirstMoment.tailPrime_low_group
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:46:35.246261+00:00
-- url     : https://prove2.me/theorems/4e1e4149-aa14-4671-a9cd-15dc879f0d34
-- title:
--   OAI.CubicFirstMoment.tailPrime_low_group: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.tailPrime_low_group` of [lean/OAI/NumberTheory/CubicMoment/Estimates/TailPrimeLowGroup.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/TailPrimeLowGroup.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem tailPrime_low_group {i j : ℕ} (s : Finset (Fin i ⊕ Fin j))
--       (hHuxley : HuxleyAdditiveLargeSieve)
--       {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
--       (hpnt : PrimaryPrimePNT) (k a : ℕ) :
--       ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
--         ∀ (z : largeTupleBoxIndex i j) (H T : ℝ),
--         let B := largeTupleGroupLength s z
--         let A := largeTupleGroupLength (Finset.univ\s) z
--         (65536:ℝ)^2 ≤ B → 4*(2*(2:ℝ)^s.card*B)^(3/2:ℝ) ≤ A →
--         (2:ℝ)^(Fintype.card {x : Fin i ⊕ Fin j // x ∉ s})*A ≤
--           B^2*(1+Real.log B)^(3*a) → A ≤ B^3 →
--         (1+Real.log (2*(2:ℝ)^s.card*B))^Ct ≤ T →
--         1 ≤ H → H ≤ B^3 →
--         ‖envelopeCutoffBilinearTail (largeTupleSelectedSupport ξ z.1.1 z.1.2 s)
--           (largeTupleOtherSupport ξ z.1.1 z.1.2 s)
--           (largeTupleSelectedCoefficient ξ z.1.1 z.1.2 s)
--           (largeTupleOtherCoefficient ξ z.1.1 z.1.2 s)
--           primeProductEnvelope H T z.1.1‖ ≤
--             K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.MontgomeryVaughanBound`, `OAI.CubicFirstMoment.largeTupleNormScale` and `OAI.CubicFirstMoment.primeProductEnvelope` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.largeTupleBoxIndex` and `OAI.CubicFirstMoment.largeTupleGroupLength` (definitions bundle `OAIQ096A006` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve` and `OAI.CubicFirstMoment.PrimaryPrimePNT` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.envelopeCutoffBilinearTail`, `OAI.CubicFirstMoment.largeTupleOtherCoefficient` and `OAI.CubicFirstMoment.largeTupleSelectedCoefficient` (definitions bundle `OAIQ096A015` of this split); `OAI.CubicFirstMoment.largeTupleOtherSupport` and `OAI.CubicFirstMoment.largeTupleSelectedSupport` (definitions bundle `OAIQ096A019` of this split).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.tailHighOrdinaryArity_isLittleO` and `OAI_CubicFirstMoment_tailPrime_ordinary_tuple_bound` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/TailPrimeLowGroup.lean (declaration OAI.CubicFirstMoment.tailPrime_low_group)

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

theorem tailPrime_low_group {i j : ℕ} (s : Finset (Fin i ⊕ Fin j))
    (hHuxley : HuxleyAdditiveLargeSieve)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hpnt : PrimaryPrimePNT) (k a : ℕ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (z : largeTupleBoxIndex i j) (H T : ℝ),
      let B := largeTupleGroupLength s z
      let A := largeTupleGroupLength (Finset.univ\s) z
      (65536:ℝ)^2 ≤ B → 4*(2*(2:ℝ)^s.card*B)^(3/2:ℝ) ≤ A →
      (2:ℝ)^(Fintype.card {x : Fin i ⊕ Fin j // x ∉ s})*A ≤
        B^2*(1+Real.log B)^(3*a) → A ≤ B^3 →
      (1+Real.log (2*(2:ℝ)^s.card*B))^Ct ≤ T →
      1 ≤ H → H ≤ B^3 →
      ‖envelopeCutoffBilinearTail (largeTupleSelectedSupport ξ z.1.1 z.1.2 s)
        (largeTupleOtherSupport ξ z.1.1 z.1.2 s)
        (largeTupleSelectedCoefficient ξ z.1.1 z.1.2 s)
        (largeTupleOtherCoefficient ξ z.1.1 z.1.2 s)
        primeProductEnvelope H T z.1.1‖ ≤
          K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k := by
  sorry

end CubicFirstMoment

end

end OAI
end
