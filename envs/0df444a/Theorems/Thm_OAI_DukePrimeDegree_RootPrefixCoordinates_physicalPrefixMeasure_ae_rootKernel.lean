-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_RootPrefixCoordinates_physicalPrefixMeasure_ae_rootKernel
-- name    : OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_ae_rootKernel
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:54:42.151913+00:00
-- url     : https://prove2.me/theorems/d6777216-58a0-4257-a7a1-4577ad5a1427
-- title:
--   OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_ae_rootKernel: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_ae_rootKernel` of [lean/OAI/NumberTheory/DukePrimeDegree/Geometry/PhysicalRectangleKernel.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Geometry/PhysicalRectangleKernel.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree.RootPrefixCoordinates`, with `open Matrix MeasureTheory ProbabilityTheory Set`, `open PrimeDegreePackets`):
--
--   ```lean
--   theorem physicalPrefixMeasure_ae_rootKernel
--       (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
--       (A : RootBox q.distinct k) (hA : A.transverse = Set.range (C.rectangleSlice q g k Q))
--       (J : Set ℝ) (hJ : IsOpen J)
--       (hwindow : ∀ w : Q.first × Q.second,
--         (Homeomorph.addRight (C.rectangleTime q g k Q w)) '' J ⊆ A.time)
--       (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
--       [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
--       (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
--         rightAction x v = x → v = 1)
--       (m : ℕ) (htime : ∀ z ∈ C.exchangedRectangleRegion q g k c hf Q J,
--         z.2 ∈ c.remainingWindow 1 m)
--       (hIH : ∀ B ∈ (C.extend q.initial q.root q.mem_remaining q.least).longBoxFamily
--           c q.next_initial hf g 1 m,
--         ∀ᵐ z ∂B.coordinateMeasure μ,
--           c.remainingGroupLeafMeasure q.next_initial hf (B.basedLeaf (1+m) μ z) =
--             c.remainingIntrinsicProduct q.next_initial hf μ
--               ((C.extend q.initial q.root q.mem_remaining q.least).timeParam c q.next_initial hf g z)) :
--       let ρ := C.physicalPrefixMeasure q g k Q A J μ
--       ∀ᵐ z ∂ρ, (ρ.map (q.prefixRootExchange d)).condKernel (z.1,z.2.2) =
--         (anchorNormalize
--           ((q.nextIntrinsicProduct d μ
--             (q.rootFiberPoint d (unrestrictedPrefixBasePoint (q := q) (C := C) (g := g)) z)).map
--               (Homeomorph.mulLeft (q.nextConjugation d z.2.2 z.2.1)))
--           ((q.nextConjugation d z.2.2) '' Q.second)).restrict
--             ((q.nextConjugation d z.2.2) '' Q.second)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DukePrimeDegree.EliminationChain`, `OAI.DukePrimeDegree.NonzeroPivots`, `OAI.DukePrimeDegree.UpperRootTransverse`, `OAI.DukePrimeDegree.ZeroPattern`, `OAI.DukePrimeDegree.allPositiveRoots`, `OAI.DukePrimeDegree.completeRootChain`, `OAI.DukePrimeDegree.positiveRootGeneratedGroup`, `OAI.PrimeDegreePackets.RootSlice`, `OAI.PrimeDegreePackets.anchorNormalize`, `OAI.PrimeDegreePackets.diagonalLogAction`, `OAI.PrimeDegreePackets.rootGroupMeasurableSpace`, `OAI.DukePrimeDegree.EliminationChain.Time`, `OAI.DukePrimeDegree.EliminationChain.finalEntries`, `OAI.DukePrimeDegree.EliminationChain.finalPivots` and `OAI.DukePrimeDegree.EliminationChain.time_measurableSpace` (definitions bundle `OAIQ244Duke011` of this split); `OAI.DukePrimeDegree.RootTransverseRectangle` (definitions bundle `OAIQ244Duke012` of this split); `OAI.DukePrimeDegree.InitialRootStep`, `OAI.DukePrimeDegree.RootPrefixCoordinates`, `OAI.PrimeDegreePackets.RootBox`, `OAI.DukePrimeDegree.EliminationChain.remainingGroupLeafMeasure`, `OAI.DukePrimeDegree.EliminationChain.remainingIntrinsicProduct`, `OAI.DukePrimeDegree.EliminationChain.remainingWindow`, `OAI.DukePrimeDegree.InitialRootStep.distinct`, `OAI.DukePrimeDegree.InitialRootStep.initial`, `OAI.DukePrimeDegree.InitialRootStep.least`, `OAI.DukePrimeDegree.InitialRootStep.mem_remaining`, `OAI.DukePrimeDegree.InitialRootStep.nextConjugation`, `OAI.DukePrimeDegree.InitialRootStep.nextIntrinsicProduct`, `OAI.DukePrimeDegree.InitialRootStep.next_initial`, `OAI.DukePrimeDegree.InitialRootStep.prefixRootExchange`, `OAI.DukePrimeDegree.InitialRootStep.processed`, `OAI.DukePrimeDegree.InitialRootStep.remaining`, `OAI.DukePrimeDegree.InitialRootStep.root`, `OAI.DukePrimeDegree.InitialRootStep.rootFiberPoint`, `OAI.DukePrimeDegree.RootPrefixCoordinates.factorPivotDomain`, `OAI.DukePrimeDegree.RootPrefixCoordinates.rectangleSlice` and `OAI.DukePrimeDegree.RootPrefixCoordinates.rectangleTime` (definitions bundle `OAIQ244Duke022` of this split); `OAI.DukePrimeDegree.RootPrefixBox`, `OAI.DukePrimeDegree.RootPrefixBox.basedLeaf`, `OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure`, `OAI.DukePrimeDegree.RootPrefixCoordinates.longBoxFamily`, `OAI.DukePrimeDegree.RootPrefixCoordinates.timeParam` and `OAI.DukePrimeDegree.RootPrefixCoordinates.unrestrictedPrefixBasePoint` (definitions bundle `OAIQ244Duke035` of this split); `OAI.DukePrimeDegree.initialRemainingErase_standardBorel` (definitions bundle `OAIQ244Duke036` of this split); `OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleRegion`, `OAI.DukePrimeDegree.RootPrefixCoordinates.extend`, `OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure` and `OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite` (definitions bundle `OAIQ244Duke044` of this split); `OAI.PrimeDegreePackets.G`, `OAI.PrimeDegreePackets.LogCoordinates`, `OAI.PrimeDegreePackets.X`, `OAI.PrimeDegreePackets.rightAction` and `OAI.PrimeDegreePackets.xMeasurableSpace` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proof of `OAI.DukePrimeDegree.PhysicalPrefixWindow.centeredConditional_product` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Geometry/PhysicalRectangleKernel.lean (declaration OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_ae_rootKernel)

import Mathlib
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke044

section

attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1))
    {D : Finset (Fin (d+1))} (c : EliminationChain (insert q.root q.processed) D)
    (hf : c.finalEntries = allPositiveRoots (d+1))

variable {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))

theorem physicalPrefixMeasure_ae_rootKernel
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k) (hA : A.transverse = Set.range (C.rectangleSlice q g k Q))
    (J : Set ℝ) (hJ : IsOpen J)
    (hwindow : ∀ w : Q.first × Q.second,
      (Homeomorph.addRight (C.rectangleTime q g k Q w)) '' J ⊆ A.time)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
      rightAction x v = x → v = 1)
    (m : ℕ) (htime : ∀ z ∈ C.exchangedRectangleRegion q g k c hf Q J,
      z.2 ∈ c.remainingWindow 1 m)
    (hIH : ∀ B ∈ (C.extend q.initial q.root q.mem_remaining q.least).longBoxFamily
        c q.next_initial hf g 1 m,
      ∀ᵐ z ∂B.coordinateMeasure μ,
        c.remainingGroupLeafMeasure q.next_initial hf (B.basedLeaf (1+m) μ z) =
          c.remainingIntrinsicProduct q.next_initial hf μ
            ((C.extend q.initial q.root q.mem_remaining q.least).timeParam c q.next_initial hf g z)) :
    let ρ := C.physicalPrefixMeasure q g k Q A J μ
    ∀ᵐ z ∂ρ, (ρ.map (q.prefixRootExchange d)).condKernel (z.1,z.2.2) =
      (anchorNormalize
        ((q.nextIntrinsicProduct d μ
          (q.rootFiberPoint d (unrestrictedPrefixBasePoint (q := q) (C := C) (g := g)) z)).map
            (Homeomorph.mulLeft (q.nextConjugation d z.2.2 z.2.1)))
        ((q.nextConjugation d z.2.2) '' Q.second)).restrict
          ((q.nextConjugation d z.2.2) '' Q.second) := by
  sorry

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end
