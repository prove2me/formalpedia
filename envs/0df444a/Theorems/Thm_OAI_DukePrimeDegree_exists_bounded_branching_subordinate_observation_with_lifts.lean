-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_exists_bounded_branching_subordinate_observation_with_lifts
-- name    : OAI.DukePrimeDegree.exists_bounded_branching_subordinate_observation_with_lifts
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:35:10.326866+00:00
-- url     : https://prove2.me/theorems/f5761c74-9cee-438d-87d3-4b64eb78df64
-- title:
--   OAI.DukePrimeDegree.exists_bounded_branching_subordinate_observation_with_lifts: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.exists_bounded_branching_subordinate_observation_with_lifts` of [lean/OAI/NumberTheory/DukePrimeDegree/Entropy/BranchingSubordinateObservation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Entropy/BranchingSubordinateObservation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree`, with `open Set MeasureTheory Filter`, `open scoped Topology BigOperators`, `open PrimeDegreePackets`):
--
--   ```lean
--   theorem exists_bounded_branching_subordinate_observation_with_lifts (d : ℕ)
--       (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
--       (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
--       (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
--       (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
--       {ε : ℝ} (hε : 0 < ε) :
--       ∃ (B r₀ : ℝ) (H Q : X (d+1) → ℕ),
--         0 < B ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧ Measurable H ∧ Measurable Q ∧
--         (∀ x, quotientLogDistance (Quotient.mk _ (1 : G (d+1))) x ≤ 2*B*(H x:ℝ)+B) ∧
--         (∀ x, Set.InjOn (fun g => rightAction x g)
--           (matrixBall (d+1) (r₀*Real.exp (-(4*B)*(H x:ℝ))))) ∧
--         (∀ m, IsCompact {x | H x ≤ m}) ∧
--         (∀ m, (Q '' {x | H x ≤ m}).Finite) ∧
--         (∀ N, observationEntropyRate μ
--           (fun x => rightAction x (diagonalOneParameter ell hell (-1))) (heightClip H N) < ε) ∧
--         (∀ x y, (∀ k : ℕ,
--           Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
--           Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
--           ∃ g ∈ matrixBall (d+1) (r₀*Real.exp (-(4*B)*(H x:ℝ))),
--             rightAction x g = y ∧ (∀ i j, ell j < ell i → g.val i j = 0) ∧
--             ∀ k : ℕ, diagonalOneParameter ell hell (k:ℝ) * g *
--               diagonalOneParameter ell hell (-(k:ℝ)) ∈
--               matrixBall (d+1) (r₀*Real.exp (-(4*B)*
--                 (H ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x):ℝ)))) ∧
--         (∀ᵐ x ∂μ, ∀ s : UpperRootTime (d+1),
--           (∀ k : ℕ,
--             Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k]
--               (rightAction x ((completeRootChain (d+1)).word s))) =
--             Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
--           s ∈ (completeRootChain (d+1)).cube 1) ∧
--         (∀ᵐ x ∂μ, ∀ᶠ s in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
--           Q ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k]
--             (rightAction x ((completeRootChain (d+1)).word s))) =
--           Q ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k] x)) ∧
--         (∀ x, H (rightAction x (diagonalOneParameter ell hell (-1))) ≤ H x+1 ∧
--           H x ≤ H (rightAction x (diagonalOneParameter ell hell (-1)))+1) ∧
--         (∀ x y, Q y=Q x → H y=H x) ∧
--         (∀ x y,
--           (∀ k : ℕ,
--             Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
--             Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
--           (∀ k : ℕ,
--             Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] y) =
--             Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] x)) →
--           ∃ g ∈ matrixBall (d+1) 1, rightAction x g=y ∧
--             ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t)) ∧
--         (∀ x y, (∀ k : ℕ,
--           Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
--           Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
--           ∃ (v : Fin (d+1) → ℝ) (hv : ∑ i, v i=0) (u : UpperRootTime (d+1)),
--             rightAction x (diagonalOneParameter v hv 1 * (completeRootChain (d+1)).word u)=y ∧
--             ∀ t : ℝ, Commute (diagonalOneParameter v hv 1) (diagonalOneParameter ell hell t)) ∧
--         UniformFinitePredecessors
--           (fun x => rightAction x (diagonalOneParameter ell hell (-1))) Q ∧
--         ∃ (J : ℕ → ℕ) (K C : ℝ), 0 < K ∧ 0 ≤ C ∧
--           (∀ m, (J m:ℝ) ≤ K*Real.exp (C*(m:ℝ))) ∧
--           ∀ m, Q '' {x | H x=m} ⊆ (Nat.pair m) '' Set.Iio (J m)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DukePrimeDegree.UpperRootTime`, `OAI.DukePrimeDegree.allPositiveRoots`, `OAI.DukePrimeDegree.completeRootChain`, `OAI.PrimeDegreePackets.diagonalOneParameter`, `OAI.PrimeDegreePackets.matrixBall`, `OAI.PrimeDegreePackets.observationEntropyRate`, `OAI.DukePrimeDegree.EliminationChain.Time`, `OAI.DukePrimeDegree.EliminationChain.cube`, `OAI.DukePrimeDegree.EliminationChain.timeTopology`, `OAI.DukePrimeDegree.EliminationChain.word` and `OAI.DukePrimeDegree.EliminationChain.zeroTime` (definitions bundle `OAIQ244Duke011` of this split); `OAI.DukePrimeDegree.UniformFinitePredecessors` and `OAI.DukePrimeDegree.heightClip` (definitions bundle `OAIQ244Duke012` of this split); `OAI.DukePrimeDegree.quotientLogDistance` (definitions bundle `OAIQ244Duke023` of this split); `OAI.PrimeDegreePackets.G`, `OAI.PrimeDegreePackets.LogCoordinates`, `OAI.PrimeDegreePackets.X`, `OAI.PrimeDegreePackets.diagonalFlow`, `OAI.PrimeDegreePackets.integralGroup`, `OAI.PrimeDegreePackets.rightAction` and `OAI.PrimeDegreePackets.xMeasurableSpace` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proof of `OAI.DukePrimeDegree.eklPrimeInput_unconditional` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Entropy/BranchingSubordinateObservation.lean (declaration OAI.DukePrimeDegree.exists_bounded_branching_subordinate_observation_with_lifts)

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
import Definitions.Def_OAIQ244Duke023

section

attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_bounded_branching_subordinate_observation_with_lifts (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (B r₀ : ℝ) (H Q : X (d+1) → ℕ),
      0 < B ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧ Measurable H ∧ Measurable Q ∧
      (∀ x, quotientLogDistance (Quotient.mk _ (1 : G (d+1))) x ≤ 2*B*(H x:ℝ)+B) ∧
      (∀ x, Set.InjOn (fun g => rightAction x g)
        (matrixBall (d+1) (r₀*Real.exp (-(4*B)*(H x:ℝ))))) ∧
      (∀ m, IsCompact {x | H x ≤ m}) ∧
      (∀ m, (Q '' {x | H x ≤ m}).Finite) ∧
      (∀ N, observationEntropyRate μ
        (fun x => rightAction x (diagonalOneParameter ell hell (-1))) (heightClip H N) < ε) ∧
      (∀ x y, (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        ∃ g ∈ matrixBall (d+1) (r₀*Real.exp (-(4*B)*(H x:ℝ))),
          rightAction x g = y ∧ (∀ i j, ell j < ell i → g.val i j = 0) ∧
          ∀ k : ℕ, diagonalOneParameter ell hell (k:ℝ) * g *
            diagonalOneParameter ell hell (-(k:ℝ)) ∈
            matrixBall (d+1) (r₀*Real.exp (-(4*B)*
              (H ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x):ℝ)))) ∧
      (∀ᵐ x ∂μ, ∀ s : UpperRootTime (d+1),
        (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k]
            (rightAction x ((completeRootChain (d+1)).word s))) =
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        s ∈ (completeRootChain (d+1)).cube 1) ∧
      (∀ᵐ x ∂μ, ∀ᶠ s in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
        Q ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k]
          (rightAction x ((completeRootChain (d+1)).word s))) =
        Q ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k] x)) ∧
      (∀ x, H (rightAction x (diagonalOneParameter ell hell (-1))) ≤ H x+1 ∧
        H x ≤ H (rightAction x (diagonalOneParameter ell hell (-1)))+1) ∧
      (∀ x y, Q y=Q x → H y=H x) ∧
      (∀ x y,
        (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] y) =
          Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] x)) →
        ∃ g ∈ matrixBall (d+1) 1, rightAction x g=y ∧
          ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t)) ∧
      (∀ x y, (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        ∃ (v : Fin (d+1) → ℝ) (hv : ∑ i, v i=0) (u : UpperRootTime (d+1)),
          rightAction x (diagonalOneParameter v hv 1 * (completeRootChain (d+1)).word u)=y ∧
          ∀ t : ℝ, Commute (diagonalOneParameter v hv 1) (diagonalOneParameter ell hell t)) ∧
      UniformFinitePredecessors
        (fun x => rightAction x (diagonalOneParameter ell hell (-1))) Q ∧
      ∃ (J : ℕ → ℕ) (K C : ℝ), 0 < K ∧ 0 ≤ C ∧
        (∀ m, (J m:ℝ) ≤ K*Real.exp (C*(m:ℝ))) ∧
        ∀ m, Q '' {x | H x=m} ⊆ (Nat.pair m) '' Set.Iio (J m) := by
  sorry

end DukePrimeDegree

end

end OAI
end
