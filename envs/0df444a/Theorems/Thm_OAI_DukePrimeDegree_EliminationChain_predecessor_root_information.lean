-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_EliminationChain_predecessor_root_information
-- name    : OAI.DukePrimeDegree.EliminationChain.predecessor_root_information
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:34:24.201176+00:00
-- url     : https://prove2.me/theorems/b64b8566-14ed-466f-bf89-3e6082708e0c
-- title:
--   OAI.DukePrimeDegree.EliminationChain.predecessor_root_information: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.EliminationChain.predecessor_root_information` of [lean/OAI/NumberTheory/DukePrimeDegree/Entropy/RootPredecessorInformation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Entropy/RootPredecessorInformation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree.EliminationChain`, with `open MeasureTheory ProbabilityTheory Set`, `open scoped ENNReal`, `open PrimeDegreePackets`):
--
--   ```lean
--   theorem predecessor_root_information
--       (d : ℕ) {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
--       (c : EliminationChain P D) (hP : InitialRootPattern P)
--       (hf : c.finalEntries=allPositiveRoots (d+1))
--       (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
--       (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
--       (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
--       (Q : X (d+1) → ℕ) (hQ : Measurable Q)
--       (κ : Kernel (X (d+1)) (X (d+1))) [IsMarkovKernel κ]
--       (hstat : μ.bind κ=μ)
--       (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x)
--       (hversion : ∀ᵐ x ∂μ, κ x=c.ambientFutureMeasure hP hf μ ell hell Q 1 x)
--       (hmass : ∀ᵐ x ∂μ,
--         0 < c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ∧
--         c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ≤ 1)
--       {M : ℕ} (B : X (d+1) → Fin (M+1)) (hB : Measurable B)
--       (href : ∀ x y, Q x=Q y →
--         Q (rightAction x (diagonalOneParameter ell hell (-1)))=
--           Q (rightAction y (diagonalOneParameter ell hell (-1))) → B x=B y)
--       (decode : ℕ → Fin (M+1) → ℕ)
--       (hdecode : ∀ x,
--         decode (Q (rightAction x (diagonalOneParameter ell hell (-1)))) (B x)=Q x) :
--       let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
--       let F := entireFutureObservation T Q
--       conditionalSigmaEntropy μ B
--         (MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance) =
--         ∑ p : ↥(allPositiveRoots (d+1) \ P),
--           (ell p.val.2-ell p.val.1)*canonicalRootCoefficient d μ p.val.1 p.val.2
--   ```
--
--   **Definitions.** The statement is written with `OAI.DukePrimeDegree.EliminationChain`, `OAI.DukePrimeDegree.InitialRootPattern`, `OAI.DukePrimeDegree.allPositiveRoots`, `OAI.PrimeDegreePackets.diagonalOneParameter`, `OAI.DukePrimeDegree.EliminationChain.Time`, `OAI.DukePrimeDegree.EliminationChain.finalEntries` and `OAI.DukePrimeDegree.EliminationChain.time_measurableSpace` (definitions bundle `OAIQ244Duke011` of this split); `OAI.DukePrimeDegree.entireFutureObservation` (definitions bundle `OAIQ244Duke012` of this split); `OAI.DukePrimeDegree.canonicalRootCoefficient`, `OAI.DukePrimeDegree.EliminationChain.ambientFutureMeasure`, `OAI.DukePrimeDegree.EliminationChain.remainingFutureAtom` and `OAI.DukePrimeDegree.EliminationChain.remainingTimeProduct` (definitions bundle `OAIQ244Duke022` of this split); `OAI.PrimeDegreePackets.conditionalSigmaEntropy` (definitions bundle `OAIQ244Duke024` of this split); `OAI.PrimeDegreePackets.LogCoordinates`, `OAI.PrimeDegreePackets.X`, `OAI.PrimeDegreePackets.diagonalFlow`, `OAI.PrimeDegreePackets.rightAction` and `OAI.PrimeDegreePackets.xMeasurableSpace` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proof of `OAI.DukePrimeDegree.RootPrefixCoordinates.predecessor_entropyRate_le_root_information_add_auxiliary` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Entropy/RootPredecessorInformation.lean (declaration OAI.DukePrimeDegree.EliminationChain.predecessor_root_information)

import Mathlib
import Mathlib.Algebra.Order.SuccPred.PartialSups
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Pairing
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Logic.Encodable.Lattice
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.PartialSups
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.MeasurableLIntegral
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
import Definitions.Def_OAIQ244Duke022
import Definitions.Def_OAIQ244Duke024

section

attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
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

namespace EliminationChain

theorem predecessor_root_information
    (d : ℕ) {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries=allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (κ : Kernel (X (d+1)) (X (d+1))) [IsMarkovKernel κ]
    (hstat : μ.bind κ=μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x)
    (hversion : ∀ᵐ x ∂μ, κ x=c.ambientFutureMeasure hP hf μ ell hell Q 1 x)
    (hmass : ∀ᵐ x ∂μ,
      0 < c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ∧
      c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ≤ 1)
    {M : ℕ} (B : X (d+1) → Fin (M+1)) (hB : Measurable B)
    (href : ∀ x y, Q x=Q y →
      Q (rightAction x (diagonalOneParameter ell hell (-1)))=
        Q (rightAction y (diagonalOneParameter ell hell (-1))) → B x=B y)
    (decode : ℕ → Fin (M+1) → ℕ)
    (hdecode : ∀ x,
      decode (Q (rightAction x (diagonalOneParameter ell hell (-1)))) (B x)=Q x) :
    let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
    let F := entireFutureObservation T Q
    conditionalSigmaEntropy μ B
      (MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance) =
      ∑ p : ↥(allPositiveRoots (d+1) \ P),
        (ell p.val.2-ell p.val.1)*canonicalRootCoefficient d μ p.val.1 p.val.2 := by
  sorry

end EliminationChain
end DukePrimeDegree

end

end OAI
end
