-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_exists_bounded_cover_subordinate_observation
-- name    : OAI.DukePrimeDegree.exists_bounded_cover_subordinate_observation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:14:26.990919+00:00
-- url     : https://prove2.me/theorems/8cf91e74-24e3-4bbb-afd1-bb6c57119035
-- title:
--   OAI.DukePrimeDegree.exists_bounded_cover_subordinate_observation: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.exists_bounded_cover_subordinate_observation` of [lean/OAI/NumberTheory/DukePrimeDegree/Entropy/CoverFutureObservation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Entropy/CoverFutureObservation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree`, with `open Set MeasureTheory Filter`, `open scoped Topology BigOperators`, `open PrimeDegreePackets`):
--
--   ```lean
--   theorem exists_bounded_cover_subordinate_observation (d : ℕ)
--       (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
--       (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
--       (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
--       (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
--       {ε : ℝ} (hε : 0 < ε) :
--       ∃ H Q : X (d+1) → ℕ, Measurable H ∧ Measurable Q ∧
--         (∀ m, IsCompact {x | H x ≤ m}) ∧
--         (∀ m, (Q '' {x | H x ≤ m}).Finite) ∧
--         (∀ N, observationEntropyRate μ
--           (fun x => rightAction x (diagonalOneParameter ell hell (-1))) (heightClip H N) < ε) ∧
--         (∀ x y, (∀ k : ℕ,
--           Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
--           Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
--           ∃ g : G (d+1), rightAction x g = y ∧
--             ∀ i j, ell j < ell i → g.val i j = 0) ∧
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
--         ∃ (J : ℕ → ℕ) (K C : ℝ), 0 < K ∧ 0 ≤ C ∧
--           (∀ m, (J m:ℝ) ≤ K*Real.exp (C*(m:ℝ))) ∧
--           ∀ m, Q '' {x | H x=m} ⊆ (Nat.pair m) '' Set.Iio (J m)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DukePrimeDegree.UpperRootTime`, `OAI.DukePrimeDegree.allPositiveRoots`, `OAI.DukePrimeDegree.completeRootChain`, `OAI.PrimeDegreePackets.diagonalOneParameter`, `OAI.PrimeDegreePackets.matrixBall`, `OAI.PrimeDegreePackets.observationEntropyRate`, `OAI.DukePrimeDegree.EliminationChain.Time`, `OAI.DukePrimeDegree.EliminationChain.cube`, `OAI.DukePrimeDegree.EliminationChain.timeTopology`, `OAI.DukePrimeDegree.EliminationChain.word` and `OAI.DukePrimeDegree.EliminationChain.zeroTime` (definitions bundle `OAIQ244Duke011` of this split); `OAI.DukePrimeDegree.heightClip` (definitions bundle `OAIQ244Duke012` of this split); `OAI.PrimeDegreePackets.G`, `OAI.PrimeDegreePackets.LogCoordinates`, `OAI.PrimeDegreePackets.X`, `OAI.PrimeDegreePackets.diagonalFlow`, `OAI.PrimeDegreePackets.integralGroup`, `OAI.PrimeDegreePackets.rightAction` and `OAI.PrimeDegreePackets.xMeasurableSpace` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proof of `OAI.DukePrimeDegree.exists_cover_stationary_wholeFutureKernel` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Entropy/CoverFutureObservation.lean (declaration OAI.DukePrimeDegree.exists_bounded_cover_subordinate_observation)

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
import Definitions.Def_OAIQ244Duke011
import Definitions.Def_OAIQ244Duke012

section

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

theorem exists_bounded_cover_subordinate_observation (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H Q : X (d+1) → ℕ, Measurable H ∧ Measurable Q ∧
      (∀ m, IsCompact {x | H x ≤ m}) ∧
      (∀ m, (Q '' {x | H x ≤ m}).Finite) ∧
      (∀ N, observationEntropyRate μ
        (fun x => rightAction x (diagonalOneParameter ell hell (-1))) (heightClip H N) < ε) ∧
      (∀ x y, (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        ∃ g : G (d+1), rightAction x g = y ∧
          ∀ i j, ell j < ell i → g.val i j = 0) ∧
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
      ∃ (J : ℕ → ℕ) (K C : ℝ), 0 < K ∧ 0 ≤ C ∧
        (∀ m, (J m:ℝ) ≤ K*Real.exp (C*(m:ℝ))) ∧
        ∀ m, Q '' {x | H x=m} ⊆ (Nat.pair m) '' Set.Iio (J m) := by
  sorry

end DukePrimeDegree

end

end OAI
end
