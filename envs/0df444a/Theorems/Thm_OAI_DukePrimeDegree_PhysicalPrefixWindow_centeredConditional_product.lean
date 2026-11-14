-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_PhysicalPrefixWindow_centeredConditional_product
-- name    : OAI.DukePrimeDegree.PhysicalPrefixWindow.centeredConditional_product
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:54:30.783804+00:00
-- url     : https://prove2.me/theorems/71fc981f-fd29-45da-919f-ff87d3f445cc
-- title:
--   OAI.DukePrimeDegree.PhysicalPrefixWindow.centeredConditional_product: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.PhysicalPrefixWindow.centeredConditional_product` of [lean/OAI/NumberTheory/DukePrimeDegree/Geometry/PhysicalWindowProduct.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Geometry/PhysicalWindowProduct.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree.PhysicalPrefixWindow`, with `open Matrix MeasureTheory ProbabilityTheory Set`, `open PrimeDegreePackets`):
--
--   ```lean
--   theorem centeredConditional_product
--       (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
--       [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
--       (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
--         rightAction x v = x → v = 1)
--       (hIH : ∀ m, ∀ A ∈ (C.extend q.initial q.root q.mem_remaining q.least).longBoxFamily
--           c' q.next_initial hf' g 1 m,
--         ∀ᵐ z ∂A.coordinateMeasure μ,
--           c'.remainingGroupLeafMeasure q.next_initial hf' (A.basedLeaf (1+m) μ z) =
--             c'.remainingIntrinsicProduct q.next_initial hf' μ
--               ((C.extend q.initial q.root q.mem_remaining q.least).timeParam c' q.next_initial hf' g z)) :
--       ∀ᵐ z ∂(B.toBox c hf).coordinateMeasure μ,
--         let a := (RootPrefixCoordinates.physicalPrefixCoordinates (T := T) q c hf).symm z
--         let x := C.timeParam c q.initial hf g z
--         c.remainingGroupLeafMeasure q.initial hf
--           (c.centeredRemainingMeasure q.initial hf ((B.toBox c hf).conditionalKernel μ z.1) z.2) =
--           (((anchorNormalize (q.nextIntrinsicProduct d μ x)
--             (q.nextFactorRebase d a.2.1 a.2.2 '' B.rectangle.second)).restrict
--               (q.nextFactorRebase d a.2.1 a.2.2 '' B.rectangle.second)).prod
--           ((anchorNormalize (intrinsicRootLeaf q.distinct μ x)
--             (Homeomorph.addRight (-a.2.2) '' B.interval)).restrict
--               (Homeomorph.addRight (-a.2.2) '' B.interval))).map q.remainingFactor
--   ```
--
--   **Definitions.** The statement is written with `OAI.DukePrimeDegree.EliminationChain`, `OAI.DukePrimeDegree.NonzeroPivots`, `OAI.DukePrimeDegree.UpperRootTransverse`, `OAI.DukePrimeDegree.ZeroPattern`, `OAI.DukePrimeDegree.allPositiveRoots`, `OAI.DukePrimeDegree.completeRootChain`, `OAI.DukePrimeDegree.positiveRootGeneratedGroup`, `OAI.PrimeDegreePackets.anchorNormalize`, `OAI.PrimeDegreePackets.diagonalLogAction`, `OAI.PrimeDegreePackets.rootGroupMeasurableSpace`, `OAI.DukePrimeDegree.EliminationChain.Time`, `OAI.DukePrimeDegree.EliminationChain.finalEntries`, `OAI.DukePrimeDegree.EliminationChain.finalPivots`, `OAI.DukePrimeDegree.EliminationChain.timeTopology` and `OAI.DukePrimeDegree.EliminationChain.time_measurableSpace` (definitions bundle `OAIQ244Duke011` of this split); `OAI.DukePrimeDegree.RootTransverseRectangle` (definitions bundle `OAIQ244Duke012` of this split); `OAI.DukePrimeDegree.InitialRootStep`, `OAI.DukePrimeDegree.RootPrefixCoordinates`, `OAI.PrimeDegreePackets.intrinsicRootLeaf`, `OAI.DukePrimeDegree.EliminationChain.centeredRemainingMeasure`, `OAI.DukePrimeDegree.EliminationChain.remainingGroupLeafMeasure`, `OAI.DukePrimeDegree.EliminationChain.remainingIntrinsicProduct`, `OAI.DukePrimeDegree.InitialRootStep.distinct`, `OAI.DukePrimeDegree.InitialRootStep.initial`, `OAI.DukePrimeDegree.InitialRootStep.least`, `OAI.DukePrimeDegree.InitialRootStep.mem_remaining`, `OAI.DukePrimeDegree.InitialRootStep.nextFactorRebase`, `OAI.DukePrimeDegree.InitialRootStep.nextIntrinsicProduct`, `OAI.DukePrimeDegree.InitialRootStep.next_initial`, `OAI.DukePrimeDegree.InitialRootStep.processed`, `OAI.DukePrimeDegree.InitialRootStep.remaining`, `OAI.DukePrimeDegree.InitialRootStep.remainingFactor`, `OAI.DukePrimeDegree.InitialRootStep.root` and `OAI.DukePrimeDegree.RootPrefixCoordinates.factorPivotDomain` (definitions bundle `OAIQ244Duke022` of this split); `OAI.DukePrimeDegree.PhysicalPrefixWindow` (definitions bundle `OAIQ244Duke034` of this split); `OAI.DukePrimeDegree.RootPrefixBox`, `OAI.DukePrimeDegree.RootPrefixBox.basedLeaf`, `OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel`, `OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure`, `OAI.DukePrimeDegree.RootPrefixCoordinates.longBoxFamily`, `OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixCoordinates` and `OAI.DukePrimeDegree.RootPrefixCoordinates.timeParam` (definitions bundle `OAIQ244Duke035` of this split); `OAI.DukePrimeDegree.PhysicalPrefixWindow.toBox` and `OAI.DukePrimeDegree.RootPrefixCoordinates.extend` (definitions bundle `OAIQ244Duke044` of this split); `OAI.PrimeDegreePackets.G`, `OAI.PrimeDegreePackets.LogCoordinates`, `OAI.PrimeDegreePackets.X`, `OAI.PrimeDegreePackets.rightAction` and `OAI.PrimeDegreePackets.xMeasurableSpace` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proofs of `OAI.DukePrimeDegree.RootPrefixBox.ae_conditionalKernel_eq_dirac_of_atomic_roots` and `OAI.DukePrimeDegree.RootPrefixBox.ae_normalized_uncentered_eq_regularLeaf` of this split import it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Geometry/PhysicalWindowProduct.lean (declaration OAI.DukePrimeDegree.PhysicalPrefixWindow.centeredConditional_product)

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

attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace PhysicalPrefixWindow
variable {d : ℕ} {q : InitialRootStep (d+1)} {T : Type*}
    [TopologicalSpace T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    {C : RootPrefixCoordinates (d+1) q.processed T} {g : G (d+1)}
    (B : PhysicalPrefixWindow q C g)
    {D D' : Finset (Fin (d+1))} (c : EliminationChain q.processed D)
    (hf : c.finalEntries = allPositiveRoots (d+1))
    (c' : EliminationChain (insert q.root q.processed) D')
    (hf' : c'.finalEntries = allPositiveRoots (d+1))

theorem centeredConditional_product
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
      rightAction x v = x → v = 1)
    (hIH : ∀ m, ∀ A ∈ (C.extend q.initial q.root q.mem_remaining q.least).longBoxFamily
        c' q.next_initial hf' g 1 m,
      ∀ᵐ z ∂A.coordinateMeasure μ,
        c'.remainingGroupLeafMeasure q.next_initial hf' (A.basedLeaf (1+m) μ z) =
          c'.remainingIntrinsicProduct q.next_initial hf' μ
            ((C.extend q.initial q.root q.mem_remaining q.least).timeParam c' q.next_initial hf' g z)) :
    ∀ᵐ z ∂(B.toBox c hf).coordinateMeasure μ,
      let a := (RootPrefixCoordinates.physicalPrefixCoordinates (T := T) q c hf).symm z
      let x := C.timeParam c q.initial hf g z
      c.remainingGroupLeafMeasure q.initial hf
        (c.centeredRemainingMeasure q.initial hf ((B.toBox c hf).conditionalKernel μ z.1) z.2) =
        (((anchorNormalize (q.nextIntrinsicProduct d μ x)
          (q.nextFactorRebase d a.2.1 a.2.2 '' B.rectangle.second)).restrict
            (q.nextFactorRebase d a.2.1 a.2.2 '' B.rectangle.second)).prod
        ((anchorNormalize (intrinsicRootLeaf q.distinct μ x)
          (Homeomorph.addRight (-a.2.2) '' B.interval)).restrict
            (Homeomorph.addRight (-a.2.2) '' B.interval))).map q.remainingFactor := by
  sorry

end PhysicalPrefixWindow
end DukePrimeDegree

end

end OAI
end
