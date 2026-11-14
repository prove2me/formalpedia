-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_RootPrefixCoordinates_predecessor_entropyRate_le_root_information_add_auxiliary
-- name    : OAI.DukePrimeDegree.RootPrefixCoordinates.predecessor_entropyRate_le_root_information_add_auxiliary
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:32:19.68732+00:00
-- url     : https://prove2.me/theorems/ffa8f8b6-590a-429c-ac7e-a7b977e3eb51
-- title:
--   OAI.DukePrimeDegree.RootPrefixCoordinates.predecessor_entropyRate_le_root_information_add_auxiliary (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.RootPrefixCoordinates.predecessor_entropyRate_le_root_information_add_auxiliary` of [lean/OAI/NumberTheory/DukePrimeDegree/Entropy/AuxiliaryRootInformation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Entropy/AuxiliaryRootInformation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree.RootPrefixCoordinates`, with `open MeasureTheory ProbabilityTheory Set`, `open PrimeDegreePackets`):
--
--   ```lean
--   theorem predecessor_entropyRate_le_root_information_add_auxiliary
--       {d : ℕ} {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
--       {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
--       [MeasurableSpace V] [BorelSpace V]
--       (C : RootPrefixCoordinates (d+1) P V) (c : EliminationChain P D)
--       (hP : InitialRootPattern P) (hf : c.finalEntries=allPositiveRoots (d+1))
--       (z₀ : (UpperRootTransverse (d+1) × V) × c.Time)
--       (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
--       [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
--       (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
--       (Q : X (d+1) → ℕ) (hQ : Measurable Q)
--       (hbound : ∀ᵐ x ∂μ, ∃ R : ℝ, ∀ v : c.Time,
--         (∀ k : ℕ, Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1]
--           (rightAction x (c.word v))) =
--           Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
--         v ∈ c.cube R)
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
--       (hdecode : ∀ x, decode (Q (rightAction x (diagonalOneParameter ell hell (-1)))) (B x)=Q x)
--       (R : X (d+1) → ℕ) (hR : Measurable R)
--       (hfinite : Summable (fun n => Real.negMulLog (μ.real {x | R x=n})))
--       (E : Set (X (d+1))) (hE : ∀ᵐ x ∂μ, x ∈ E)
--       (hrelative : ∀ x ∈ E, ∀ y ∈ E,
--         (∀ k : ℕ, Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1] y)=
--           Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
--         (∀ k : ℕ, R ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1] y)=
--           R ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
--         ∃ u : c.Time, rightAction x (c.word u)=y)
--       (L : ℕ) :
--       observationEntropyRate μ (fun x => rightAction x (diagonalOneParameter ell hell (-1)))
--         (heightClip Q L) ≤
--         (∑ p : ↥(allPositiveRoots (d+1) \ P),
--           (ell p.val.2-ell p.val.1)*canonicalRootCoefficient d μ p.val.1 p.val.2) +
--         ∑' n, Real.negMulLog (μ.real {x | R x=n})
--   ```
--
--   **Definitions.** The statement is written with `OAI.DukePrimeDegree.EliminationChain`, `OAI.DukePrimeDegree.InitialRootPattern`, `OAI.DukePrimeDegree.UpperRootTransverse`, `OAI.DukePrimeDegree.allPositiveRoots`, `OAI.PrimeDegreePackets.diagonalLogAction`, `OAI.PrimeDegreePackets.diagonalOneParameter`, `OAI.PrimeDegreePackets.observationEntropyRate`, `OAI.DukePrimeDegree.EliminationChain.Time`, `OAI.DukePrimeDegree.EliminationChain.cube`, `OAI.DukePrimeDegree.EliminationChain.finalEntries`, `OAI.DukePrimeDegree.EliminationChain.time_measurableSpace` and `OAI.DukePrimeDegree.EliminationChain.word` (definitions bundle `OAIQ244Duke011` of this split); `OAI.DukePrimeDegree.heightClip` (definitions bundle `OAIQ244Duke012` of this split); `OAI.DukePrimeDegree.RootPrefixCoordinates`, `OAI.DukePrimeDegree.canonicalRootCoefficient`, `OAI.DukePrimeDegree.EliminationChain.ambientFutureMeasure`, `OAI.DukePrimeDegree.EliminationChain.remainingFutureAtom` and `OAI.DukePrimeDegree.EliminationChain.remainingTimeProduct` (definitions bundle `OAIQ244Duke022` of this split); `OAI.PrimeDegreePackets.LogCoordinates`, `OAI.PrimeDegreePackets.X`, `OAI.PrimeDegreePackets.rightAction` and `OAI.PrimeDegreePackets.xMeasurableSpace` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proof of `OAI.DukePrimeDegree.negative_diagonal_entropy_le_root_sum_of_small_auxiliary` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Entropy/AuxiliaryRootInformation.lean (declaration OAI.DukePrimeDegree.RootPrefixCoordinates.predecessor_entropyRate_le_root_information_add_auxiliary)

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
import Mathlib.Topology.Bases
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

section

attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates

theorem predecessor_entropyRate_le_root_information_add_auxiliary
    {d : ℕ} {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V]
    (C : RootPrefixCoordinates (d+1) P V) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries=allPositiveRoots (d+1))
    (z₀ : (UpperRootTransverse (d+1) × V) × c.Time)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (hbound : ∀ᵐ x ∂μ, ∃ R : ℝ, ∀ v : c.Time,
      (∀ k : ℕ, Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1]
        (rightAction x (c.word v))) =
        Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
      v ∈ c.cube R)
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
    (hdecode : ∀ x, decode (Q (rightAction x (diagonalOneParameter ell hell (-1)))) (B x)=Q x)
    (R : X (d+1) → ℕ) (hR : Measurable R)
    (hfinite : Summable (fun n => Real.negMulLog (μ.real {x | R x=n})))
    (E : Set (X (d+1))) (hE : ∀ᵐ x ∂μ, x ∈ E)
    (hrelative : ∀ x ∈ E, ∀ y ∈ E,
      (∀ k : ℕ, Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1] y)=
        Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
      (∀ k : ℕ, R ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1] y)=
        R ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
      ∃ u : c.Time, rightAction x (c.word u)=y)
    (L : ℕ) :
    observationEntropyRate μ (fun x => rightAction x (diagonalOneParameter ell hell (-1)))
      (heightClip Q L) ≤
      (∑ p : ↥(allPositiveRoots (d+1) \ P),
        (ell p.val.2-ell p.val.1)*canonicalRootCoefficient d μ p.val.1 p.val.2) +
      ∑' n, Real.negMulLog (μ.real {x | R x=n}) := by
  sorry

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end
