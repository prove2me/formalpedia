-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_PhysicalPrefixWindow_independent
-- name    : OAI.DukePrimeDegree.PhysicalPrefixWindow.independent
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:54:51.658204+00:00
-- url     : https://prove2.me/theorems/0e4730fc-07ad-4d4b-a003-e6653ca1965a
-- title:
--   OAI.DukePrimeDegree.PhysicalPrefixWindow.independent: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.PhysicalPrefixWindow.independent` of [lean/OAI/NumberTheory/DukePrimeDegree/Geometry/PhysicalPrefixWindows.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Geometry/PhysicalPrefixWindows.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree.PhysicalPrefixWindow`, with `open Matrix MeasureTheory ProbabilityTheory Set`, `open PrimeDegreePackets`):
--
--   ```lean
--   theorem independent (B : PhysicalPrefixWindow q C g)
--       (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
--       (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
--       letI : Nonempty B.rectangle.second := B.second_nonempty.to_subtype
--       haveI : StandardBorelSpace B.rectangle.second := B.rectangle.second_open.measurableSet.standardBorel
--       let σ := shiftedRootFactorPullback q.distinct B.box μ
--         (C.rectangleSlice q g B.pivot B.rectangle) (C.rectangleTime q g B.pivot B.rectangle)
--       haveI := shiftedRootFactorPullback_finite q.distinct B.box μ
--         (C.rectangleSlice q g B.pivot B.rectangle)
--         (C.rectangleSlice_isOpenEmbedding q g B.pivot B.rectangle).measurableEmbedding
--         (C.rectangleTime q g B.pivot B.rectangle)
--         (C.continuous_rectangleTime q g B.pivot B.rectangle).measurable
--       let ρ := σ.restrict (univ ×ˢ (univ ×ˢ B.interval))
--       ∀ᵐ s ∂ρ.fst, ρ.condKernel s = (ρ.condKernel s).fst.prod (ρ.condKernel s).snd
--   ```
--
--   **Definitions.** The statement is written with `OAI.DukePrimeDegree.NonzeroPivots`, `OAI.DukePrimeDegree.UpperRootTransverse`, `OAI.DukePrimeDegree.ZeroPattern`, `OAI.DukePrimeDegree.completeRootChain`, `OAI.DukePrimeDegree.positiveRootGeneratedGroup`, `OAI.PrimeDegreePackets.RootSlice`, `OAI.PrimeDegreePackets.rootGroupBorelSpace`, `OAI.PrimeDegreePackets.rootGroupMeasurableSpace`, `OAI.DukePrimeDegree.EliminationChain.finalEntries` and `OAI.DukePrimeDegree.EliminationChain.finalPivots` (definitions bundle `OAIQ244Duke011` of this split); `OAI.DukePrimeDegree.RootTransverseRectangle` (definitions bundle `OAIQ244Duke012` of this split); `OAI.DukePrimeDegree.InitialRootStep`, `OAI.DukePrimeDegree.RootPrefixCoordinates`, `OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable`, `OAI.DukePrimeDegree.InitialRootStep.distinct`, `OAI.DukePrimeDegree.InitialRootStep.processed`, `OAI.DukePrimeDegree.InitialRootStep.remaining`, `OAI.DukePrimeDegree.InitialRootStep.root`, `OAI.DukePrimeDegree.RootPrefixCoordinates.factorPivotDomain`, `OAI.DukePrimeDegree.RootPrefixCoordinates.rectangleSlice` and `OAI.DukePrimeDegree.RootPrefixCoordinates.rectangleTime` (definitions bundle `OAIQ244Duke022` of this split); `OAI.DukePrimeDegree.upperRootTransverse_secondCountable` (definitions bundle `OAIQ244Duke023` of this split); `OAI.DukePrimeDegree.PhysicalPrefixWindow` (definitions bundle `OAIQ244Duke034` of this split); `OAI.DukePrimeDegree.shiftedRootFactorPullback` and `OAI.DukePrimeDegree.shiftedRootFactorPullback_finite` (definitions bundle `OAIQ244Duke035` of this split); `OAI.DukePrimeDegree.initialRemainingErase_standardBorel` (definitions bundle `OAIQ244Duke036` of this split); `OAI.DukePrimeDegree.RootPrefixCoordinates.continuous_rectangleTime` and `OAI.DukePrimeDegree.RootPrefixCoordinates.rectangleSlice_isOpenEmbedding` (definitions bundle `OAIQ244Duke044` of this split); `OAI.PrimeDegreePackets.G`, `OAI.PrimeDegreePackets.LogCoordinates`, `OAI.PrimeDegreePackets.X`, `OAI.PrimeDegreePackets.diagonalFlow`, `OAI.PrimeDegreePackets.rightAction` and `OAI.PrimeDegreePackets.xMeasurableSpace` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proof of `OAI.DukePrimeDegree.PhysicalPrefixWindow.centeredConditional_product` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Geometry/PhysicalPrefixWindows.lean (declaration OAI.DukePrimeDegree.PhysicalPrefixWindow.independent)

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

attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
variable {d : ℕ} {q : InitialRootStep (d+1)} {T : Type*} [TopologicalSpace T]
    {C : RootPrefixCoordinates (d+1) q.processed T} {g : G (d+1)}

variable [MeasurableSpace T] [BorelSpace T]

theorem independent (B : PhysicalPrefixWindow q C g)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    letI : Nonempty B.rectangle.second := B.second_nonempty.to_subtype
    haveI : StandardBorelSpace B.rectangle.second := B.rectangle.second_open.measurableSet.standardBorel
    let σ := shiftedRootFactorPullback q.distinct B.box μ
      (C.rectangleSlice q g B.pivot B.rectangle) (C.rectangleTime q g B.pivot B.rectangle)
    haveI := shiftedRootFactorPullback_finite q.distinct B.box μ
      (C.rectangleSlice q g B.pivot B.rectangle)
      (C.rectangleSlice_isOpenEmbedding q g B.pivot B.rectangle).measurableEmbedding
      (C.rectangleTime q g B.pivot B.rectangle)
      (C.continuous_rectangleTime q g B.pivot B.rectangle).measurable
    let ρ := σ.restrict (univ ×ˢ (univ ×ˢ B.interval))
    ∀ᵐ s ∂ρ.fst, ρ.condKernel s = (ρ.condKernel s).fst.prod (ρ.condKernel s).snd := by
  sorry

end PhysicalPrefixWindow

end DukePrimeDegree

end

end OAI
end
