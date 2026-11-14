-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_countable_patch_name_entropy_sublinear
-- name    : OAI.DukePrimeDegree.countable_patch_name_entropy_sublinear
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:33:00.993767+00:00
-- url     : https://prove2.me/theorems/16f04e3e-3530-46ba-b4be-7e09bdd57b74
-- title:
--   OAI.DukePrimeDegree.countable_patch_name_entropy_sublinear: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.countable_patch_name_entropy_sublinear` of [lean/OAI/NumberTheory/DukePrimeDegree/Entropy/CountablePatchEntropy.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Entropy/CountablePatchEntropy.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology BigOperators`, `open PrimeDegreePackets`):
--
--   ```lean
--   theorem countable_patch_name_entropy_sublinear {n k : ℕ}
--       (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
--       (Q : X n → ℕ) (hQ : Measurable Q)
--       (E : ℕ → Set (X n)) (hE : ∀ i, MeasurableSet (E i))
--       (hpair : ∀ i, ∀ x ∈ E i, ∀ y ∈ E i,
--         fullFutureObservation
--           (fun z => rightAction z (diagonalOneParameter ell hell (-1))) Q 0 x =
--         fullFutureObservation
--           (fun z => rightAction z (diagonalOneParameter ell hell (-1))) Q 0 y →
--         ∃ g ∈ matrixBall n 1, rightAction x g=y ∧
--           ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t))
--       (μ : Measure (X n)) [IsProbabilityMeasure μ]
--       (hfull : ∀ᵐ y ∂μ, y ∈ ⋃ i, E i)
--       (hT : MeasurePreserving
--         (fun z => rightAction z (diagonalOneParameter ell hell (-1))) μ μ)
--       (P : X n → Fin k) (hP : Measurable P)
--       {ε : ℝ} (hε : 0 < ε) :
--       ∃ C : ℝ, ∀ N : ℕ,
--         conditionalSigmaEntropy μ
--           (orbitName (fun z => rightAction z (diagonalOneParameter ell hell (-1))) P N)
--           (fullFutureSigma
--             (fun z => rightAction z (diagonalOneParameter ell hell (-1))) Q N) ≤ C+N*ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.DukePrimeDegree.fullFutureObservation` (definitions bundle `OAIQ244Duke008` of this split); `OAI.PrimeDegreePackets.diagonalOneParameter`, `OAI.PrimeDegreePackets.matrixBall` and `OAI.PrimeDegreePackets.orbitName` (definitions bundle `OAIQ244Duke011` of this split); `OAI.DukePrimeDegree.fullFutureSigma` (definitions bundle `OAIQ244Duke012` of this split); `OAI.PrimeDegreePackets.conditionalSigmaEntropy` (definitions bundle `OAIQ244Duke024` of this split); `OAI.PrimeDegreePackets.G`, `OAI.PrimeDegreePackets.X`, `OAI.PrimeDegreePackets.rightAction` and `OAI.PrimeDegreePackets.xMeasurableSpace` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proof of `OAI.DukePrimeDegree.diagonal_entropy_zero_of_atomic_positive_roots` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Entropy/CountablePatchEntropy.lean (declaration OAI.DukePrimeDegree.countable_patch_name_entropy_sublinear)

import Mathlib
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Pairing
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
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
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke024

section

attribute [-instance] _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

theorem countable_patch_name_entropy_sublinear {n k : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (hQ : Measurable Q)
    (E : ℕ → Set (X n)) (hE : ∀ i, MeasurableSet (E i))
    (hpair : ∀ i, ∀ x ∈ E i, ∀ y ∈ E i,
      fullFutureObservation
        (fun z => rightAction z (diagonalOneParameter ell hell (-1))) Q 0 x =
      fullFutureObservation
        (fun z => rightAction z (diagonalOneParameter ell hell (-1))) Q 0 y →
      ∃ g ∈ matrixBall n 1, rightAction x g=y ∧
        ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t))
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (hfull : ∀ᵐ y ∂μ, y ∈ ⋃ i, E i)
    (hT : MeasurePreserving
      (fun z => rightAction z (diagonalOneParameter ell hell (-1))) μ μ)
    (P : X n → Fin k) (hP : Measurable P)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ N : ℕ,
      conditionalSigmaEntropy μ
        (orbitName (fun z => rightAction z (diagonalOneParameter ell hell (-1))) P N)
        (fullFutureSigma
          (fun z => rightAction z (diagonalOneParameter ell hell (-1))) Q N) ≤ C+N*ε := by
  sorry

end DukePrimeDegree

end

end OAI
end
