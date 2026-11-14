-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_exists_compact_equal_leaf_shearing_sequence
-- name    : OAI.DukePrimeDegree.exists_compact_equal_leaf_shearing_sequence
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:47:17.514207+00:00
-- url     : https://prove2.me/theorems/129a2287-573d-4cda-83f2-b49df87ddcc1
-- title:
--   OAI.DukePrimeDegree.exists_compact_equal_leaf_shearing_sequence: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.exists_compact_equal_leaf_shearing_sequence` of [lean/OAI/NumberTheory/DukePrimeDegree/Dynamics/CompactShearingSequence.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Dynamics/CompactShearingSequence.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree`, with `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open PrimeDegreePackets`):
--
--   ```lean
--   theorem exists_compact_equal_leaf_shearing_sequence
--       (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
--       (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
--       (hfree : ∀ᵐ x ∂μ, ∀ u : ℝ,
--         rightAction x (Matrix.SpecialLinearGroup.transvection hij u) = x → u = 0)
--       (g : ℕ → G (d + 1)) (hg : Tendsto g atTop (𝓝 1))
--       (hnot : ∀ m, ¬ ∀ t : ℝ, g m * Matrix.SpecialLinearGroup.transvection hij t =
--         Matrix.SpecialLinearGroup.transvection hij t * g m)
--       (hsmall : ∀ m, rootShearingKappa i j (g m) ≤ 1)
--       (hT : ∀ m, 1 ≤ rootShearingLogTime i j (g m))
--       (C : ℝ) (hC : 1 ≤ C) (hlog : ∀ m, Real.log C ≤ rootShearingLogTime i j (g m))
--       (K G H : Set (X (d + 1))) (z : ℕ → Fin 2 → X (d + 1))
--       (hpair : ∀ m, rightAction (z m 0) (g m) = z m 1)
--       (ρ ε : ℝ) (c a : ℝ≥0∞) (hε : 72 * ε < 1)
--       (hsecond : 16 / ρ ≤ ρ * C) (hcoeff : c + c + a < 1)
--       (hregular : ∀ x ∈ G,
--         intrinsicRootKernel hij μ hfree x = intrinsicRootLeaf hij μ x ∧
--         IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x) ∧
--         ∀ᵐ t ∂intrinsicRootLeaf hij μ x,
--           intrinsicRootLeaf hij μ (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
--             basedRealMeasure (intrinsicRootLeaf hij μ x) t)
--       (hgood : ∀ x ∈ G, ∀ r : ℝ, 0 < r →
--         intrinsicRootLeaf hij μ x (rootHitTimes hij Kᶜ x ∩ Metric.closedBall 0 r) ≤
--           c * intrinsicRootLeaf hij μ x (Metric.closedBall 0 r))
--       (hHsmall : ∀ y ∈ H, intrinsicRootKernel hij μ hfree y (Metric.closedBall 0 ρ) < a)
--       (hpos : ∀ m k, ∀ r : ℝ, 0 < r →
--         0 < intrinsicRootKernel hij μ hfree (z m k) (Metric.ball 0 r))
--       (heq : ∀ m, intrinsicRootKernel hij μ hfree (z m 0) =
--         intrinsicRootKernel hij μ hfree (z m 1))
--       (hcov : ∀ m k, ∀ᵐ t : ℝ ∂volume, RootPairLeafCovariance hij μ hfree (z m k) t)
--       (hcontrol : ∀ m k, ∀ S : ℝ, 1 ≤ S →
--         volume.real (Ioc 0 S ∩ {t | rightAction (z m k) (rootPairFlow i j (-t)) ∉ G}) ≤ ε * S ∧
--         volume.real (Ioc 0 S ∩ {t | rightAction (z m k) (rootPairFlow i j (-t)) ∉ H}) ≤ ε * S) :
--       ∃ (γ : ℕ → PrimeDegreePackets.G (d + 1))
--         (p : ℕ → Fin 2 → X (d + 1)) (t : ℕ → Fin 2 → ℝ),
--         Tendsto γ atTop (𝓝 1) ∧ ∀ m,
--           0 < rootShearingKappa i j (γ m) ∧ rootShearingKappa i j (γ m) ≤ 1 ∧
--           (∀ b, p m b ∈ K ∧
--             rightAction (p m b) (Matrix.SpecialLinearGroup.transvection hij (t m b) * γ m *
--               Matrix.SpecialLinearGroup.transvection hij (-t m b)) ∈ K ∧
--             intrinsicRootLeaf hij μ (p m b) = intrinsicRootLeaf hij μ
--               (rightAction (p m b) (Matrix.SpecialLinearGroup.transvection hij (t m b) * γ m *
--                 Matrix.SpecialLinearGroup.transvection hij (-t m b)))) ∧
--           ρ ≤ |rootShearingKappa i j (γ m) * t m 0| ∧
--           |rootShearingKappa i j (γ m) * t m 0| ≤ 1 ∧
--           16 / ρ ≤ |rootShearingKappa i j (γ m) * t m 1| ∧
--           |rootShearingKappa i j (γ m) * t m 1| ≤ C
--   ```
--
--   **Definitions.** The statement is written with `OAI.PrimeDegreePackets.basedRealMeasure` (definitions bundle `OAIQ244Duke011` of this split); `OAI.PrimeDegreePackets.intrinsicRootLeaf` (definitions bundle `OAIQ244Duke022` of this split); `OAI.DukePrimeDegree.rootHitTimes`, `OAI.DukePrimeDegree.rootPairFlow`, `OAI.DukePrimeDegree.rootShearingKappa` and `OAI.DukePrimeDegree.rootShearingLogTime` (definitions bundle `OAIQ244Duke023` of this split); `OAI.DukePrimeDegree.RootPairLeafCovariance` and `OAI.PrimeDegreePackets.intrinsicRootKernel` (definitions bundle `OAIQ244Duke035` of this split); `OAI.PrimeDegreePackets.G`, `OAI.PrimeDegreePackets.X`, `OAI.PrimeDegreePackets.rightAction` and `OAI.PrimeDegreePackets.xMeasurableSpace` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proof of `OAI.DukePrimeDegree.exists_distinct_equal_leaf_horospherical_pair` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Dynamics/CompactShearingSequence.lean (declaration OAI.DukePrimeDegree.exists_compact_equal_leaf_shearing_sequence)

import Mathlib
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke035

section

attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_compact_equal_leaf_shearing_sequence
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ u : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij u) = x → u = 0)
    (g : ℕ → G (d + 1)) (hg : Tendsto g atTop (𝓝 1))
    (hnot : ∀ m, ¬ ∀ t : ℝ, g m * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g m)
    (hsmall : ∀ m, rootShearingKappa i j (g m) ≤ 1)
    (hT : ∀ m, 1 ≤ rootShearingLogTime i j (g m))
    (C : ℝ) (hC : 1 ≤ C) (hlog : ∀ m, Real.log C ≤ rootShearingLogTime i j (g m))
    (K G H : Set (X (d + 1))) (z : ℕ → Fin 2 → X (d + 1))
    (hpair : ∀ m, rightAction (z m 0) (g m) = z m 1)
    (ρ ε : ℝ) (c a : ℝ≥0∞) (hε : 72 * ε < 1)
    (hsecond : 16 / ρ ≤ ρ * C) (hcoeff : c + c + a < 1)
    (hregular : ∀ x ∈ G,
      intrinsicRootKernel hij μ hfree x = intrinsicRootLeaf hij μ x ∧
      IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x) ∧
      ∀ᵐ t ∂intrinsicRootLeaf hij μ x,
        intrinsicRootLeaf hij μ (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
          basedRealMeasure (intrinsicRootLeaf hij μ x) t)
    (hgood : ∀ x ∈ G, ∀ r : ℝ, 0 < r →
      intrinsicRootLeaf hij μ x (rootHitTimes hij Kᶜ x ∩ Metric.closedBall 0 r) ≤
        c * intrinsicRootLeaf hij μ x (Metric.closedBall 0 r))
    (hHsmall : ∀ y ∈ H, intrinsicRootKernel hij μ hfree y (Metric.closedBall 0 ρ) < a)
    (hpos : ∀ m k, ∀ r : ℝ, 0 < r →
      0 < intrinsicRootKernel hij μ hfree (z m k) (Metric.ball 0 r))
    (heq : ∀ m, intrinsicRootKernel hij μ hfree (z m 0) =
      intrinsicRootKernel hij μ hfree (z m 1))
    (hcov : ∀ m k, ∀ᵐ t : ℝ ∂volume, RootPairLeafCovariance hij μ hfree (z m k) t)
    (hcontrol : ∀ m k, ∀ S : ℝ, 1 ≤ S →
      volume.real (Ioc 0 S ∩ {t | rightAction (z m k) (rootPairFlow i j (-t)) ∉ G}) ≤ ε * S ∧
      volume.real (Ioc 0 S ∩ {t | rightAction (z m k) (rootPairFlow i j (-t)) ∉ H}) ≤ ε * S) :
    ∃ (γ : ℕ → PrimeDegreePackets.G (d + 1))
      (p : ℕ → Fin 2 → X (d + 1)) (t : ℕ → Fin 2 → ℝ),
      Tendsto γ atTop (𝓝 1) ∧ ∀ m,
        0 < rootShearingKappa i j (γ m) ∧ rootShearingKappa i j (γ m) ≤ 1 ∧
        (∀ b, p m b ∈ K ∧
          rightAction (p m b) (Matrix.SpecialLinearGroup.transvection hij (t m b) * γ m *
            Matrix.SpecialLinearGroup.transvection hij (-t m b)) ∈ K ∧
          intrinsicRootLeaf hij μ (p m b) = intrinsicRootLeaf hij μ
            (rightAction (p m b) (Matrix.SpecialLinearGroup.transvection hij (t m b) * γ m *
              Matrix.SpecialLinearGroup.transvection hij (-t m b)))) ∧
        ρ ≤ |rootShearingKappa i j (γ m) * t m 0| ∧
        |rootShearingKappa i j (γ m) * t m 0| ≤ 1 ∧
        16 / ρ ≤ |rootShearingKappa i j (γ m) * t m 1| ∧
        |rootShearingKappa i j (γ m) * t m 1| ≤ C := by
  sorry

end DukePrimeDegree

end

end OAI
end
