-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_exists_small_future_observation
-- name    : OAI.DukePrimeDegree.exists_small_future_observation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:38:44.243053+00:00
-- url     : https://prove2.me/theorems/91d84eb6-5096-4e50-82a1-f1e0059350c2
-- title:
--   OAI.DukePrimeDegree.exists_small_future_observation: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.exists_small_future_observation` of [lean/OAI/NumberTheory/DukePrimeDegree/Entropy/SmallFutureObservation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Entropy/SmallFutureObservation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree`, with `open MeasureTheory Set`, `open scoped Topology`, `open PrimeDegreePackets`):
--
--   ```lean
--   theorem exists_small_future_observation (d : ℕ)
--       (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
--       (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
--       (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
--       (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ) :
--       ∃ (H Q : X (d+1) → ℕ) (r : ℕ → ℝ),
--         Measurable H ∧ Measurable Q ∧ Antitone r ∧
--         (∀ m, 0 < r m ∧ r m ≤ 1) ∧
--         (∀ x, LocalInjectivityAt (r (H x)) x) ∧
--         UniformFinitePredecessors
--           (fun x => rightAction x (diagonalOneParameter ell hell (-1))) Q ∧
--         (∀ x y, (∀ k : ℕ,
--           Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
--           Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
--           ∃ g ∈ matrixBall (d+1) (r (H x)), rightAction x g=y ∧
--             ∀ i j, ell j < ell i → g.val i j=0) ∧
--         (∀ x y,
--           (∀ k : ℕ,
--             Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
--             Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
--           (∀ k : ℕ,
--             Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] y) =
--             Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] x)) →
--           ∃ g ∈ matrixBall (d+1) 1, rightAction x g=y ∧
--             ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t))
--   ```
--
--   **Definitions.** The statement is written with `OAI.DukePrimeDegree.allPositiveRoots`, `OAI.PrimeDegreePackets.diagonalOneParameter` and `OAI.PrimeDegreePackets.matrixBall` (definitions bundle `OAIQ244Duke011` of this split); `OAI.DukePrimeDegree.UniformFinitePredecessors` (definitions bundle `OAIQ244Duke012` of this split); `OAI.DukePrimeDegree.LocalInjectivityAt` (definitions bundle `OAIQ244Duke022` of this split); `OAI.PrimeDegreePackets.G`, `OAI.PrimeDegreePackets.LogCoordinates`, `OAI.PrimeDegreePackets.X`, `OAI.PrimeDegreePackets.diagonalFlow`, `OAI.PrimeDegreePackets.rightAction` and `OAI.PrimeDegreePackets.xMeasurableSpace` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proof of `OAI.DukePrimeDegree.diagonal_entropy_zero_of_atomic_positive_roots` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Entropy/SmallFutureObservation.lean (declaration OAI.DukePrimeDegree.exists_small_future_observation)

import Mathlib
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Pairwise.Basic
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

section

attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_small_future_observation (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ) :
    ∃ (H Q : X (d+1) → ℕ) (r : ℕ → ℝ),
      Measurable H ∧ Measurable Q ∧ Antitone r ∧
      (∀ m, 0 < r m ∧ r m ≤ 1) ∧
      (∀ x, LocalInjectivityAt (r (H x)) x) ∧
      UniformFinitePredecessors
        (fun x => rightAction x (diagonalOneParameter ell hell (-1))) Q ∧
      (∀ x y, (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        ∃ g ∈ matrixBall (d+1) (r (H x)), rightAction x g=y ∧
          ∀ i j, ell j < ell i → g.val i j=0) ∧
      (∀ x y,
        (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] y) =
          Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] x)) →
        ∃ g ∈ matrixBall (d+1) 1, rightAction x g=y ∧
          ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t)) := by
  sorry

end DukePrimeDegree

end

end OAI
end
