-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_RootPrefixBox_ae_normalized_uncentered_eq_regularLeaf
-- name    : OAI.DukePrimeDegree.RootPrefixBox.ae_normalized_uncentered_eq_regularLeaf
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:46:37.868524+00:00
-- url     : https://prove2.me/theorems/99334418-d584-4086-a2f8-a76a3572d45c
-- title:
--   OAI.DukePrimeDegree.RootPrefixBox.ae_normalized_uncentered_eq_regularLeaf: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.RootPrefixBox.ae_normalized_uncentered_eq_regularLeaf` of [lean/OAI/NumberTheory/DukePrimeDegree/Geometry/RootPrefixTransverseProduct.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Geometry/RootPrefixTransverseProduct.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree.RootPrefixBox`, with `open MeasureTheory ProbabilityTheory Set`, `open scoped ENNReal`, `open PrimeDegreePackets`):
--
--   ```lean
--   theorem ae_normalized_uncentered_eq_regularLeaf
--       (B : RootPrefixBox C c hP hf g) (R : ℝ) (hBR : B.time ⊆ c.remainingWindow R 0)
--       (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
--       [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
--       (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
--         rightAction x v = x → v = 1) :
--       ∀ᵐ z ∂B.coordinateMeasure μ, ∀ J : Set c.Time,
--         anchorNormalize (B.uncenteredIntrinsicProduct μ z) J =
--           anchorNormalize (B.regularLeafKernel R hBR μ hfree z.1) J
--   ```
--
--   **Definitions.** The statement is written with `OAI.DukePrimeDegree.EliminationChain`, `OAI.DukePrimeDegree.InitialRootPattern`, `OAI.DukePrimeDegree.NonzeroPivots`, `OAI.DukePrimeDegree.UpperRootTransverse`, `OAI.DukePrimeDegree.ZeroPattern`, `OAI.DukePrimeDegree.allPositiveRoots`, `OAI.DukePrimeDegree.completeRootChain`, `OAI.DukePrimeDegree.positiveRootGeneratedGroup`, `OAI.PrimeDegreePackets.anchorNormalize`, `OAI.PrimeDegreePackets.diagonalLogAction`, `OAI.PrimeDegreePackets.rootGroupMeasurableSpace`, `OAI.DukePrimeDegree.EliminationChain.Time`, `OAI.DukePrimeDegree.EliminationChain.finalEntries`, `OAI.DukePrimeDegree.EliminationChain.finalPivots` and `OAI.DukePrimeDegree.EliminationChain.time_measurableSpace` (definitions bundle `OAIQ244Duke011` of this split); `OAI.DukePrimeDegree.RootPrefixCoordinates` and `OAI.DukePrimeDegree.EliminationChain.remainingWindow` (definitions bundle `OAIQ244Duke022` of this split); `OAI.DukePrimeDegree.RootPrefixBox`, `OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure`, `OAI.DukePrimeDegree.RootPrefixBox.regularLeafKernel` and `OAI.DukePrimeDegree.RootPrefixBox.uncenteredIntrinsicProduct` (definitions bundle `OAIQ244Duke035` of this split); `OAI.PrimeDegreePackets.G`, `OAI.PrimeDegreePackets.LogCoordinates`, `OAI.PrimeDegreePackets.X`, `OAI.PrimeDegreePackets.rightAction` and `OAI.PrimeDegreePackets.xMeasurableSpace` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proofs of `OAI.DukePrimeDegree.RootPrefixBox.selfConstant_image_massContained`, `OAI.DukePrimeDegree.RootPrefixCoordinates.predecessor_entropyRate_le_root_information_add_auxiliary`, `OAI.DukePrimeDegree.RootPrefixCoordinates.wholeFutureKernel_stationary` and `OAI.DukePrimeDegree.exists_cover_stationary_wholeFutureKernel` of this split import it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Geometry/RootPrefixTransverseProduct.lean (declaration OAI.DukePrimeDegree.RootPrefixBox.ae_normalized_uncentered_eq_regularLeaf)

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
import Definitions.Def_OAIQ244Duke035

section

attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox

variable {d : ℕ} {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {hP : InitialRootPattern P} {c : EliminationChain P D}
    {hf : c.finalEntries = allPositiveRoots (d+1)}
    {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    {C : RootPrefixCoordinates (d+1) P T} {g : G (d+1)}

theorem ae_normalized_uncentered_eq_regularLeaf
    (B : RootPrefixBox C c hP hf g) (R : ℝ) (hBR : B.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
      rightAction x v = x → v = 1) :
    ∀ᵐ z ∂B.coordinateMeasure μ, ∀ J : Set c.Time,
      anchorNormalize (B.uncenteredIntrinsicProduct μ z) J =
        anchorNormalize (B.regularLeafKernel R hBR μ hfree z.1) J := by
  sorry

end RootPrefixBox
end DukePrimeDegree

end

end OAI
end
