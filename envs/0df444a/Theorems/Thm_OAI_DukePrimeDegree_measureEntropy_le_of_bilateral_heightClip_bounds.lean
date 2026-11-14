-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_measureEntropy_le_of_bilateral_heightClip_bounds
-- name    : OAI.DukePrimeDegree.measureEntropy_le_of_bilateral_heightClip_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:39:31.984204+00:00
-- url     : https://prove2.me/theorems/d1c17475-ebd2-4ad6-a02a-e9cd14890c17
-- title:
--   OAI.DukePrimeDegree.measureEntropy_le_of_bilateral_heightClip_bounds: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.measureEntropy_le_of_bilateral_heightClip_bounds` of [lean/OAI/NumberTheory/DukePrimeDegree/Entropy/BilateralFiniteCodes.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Entropy/BilateralFiniteCodes.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree`, with `open MeasureTheory Set Filter`, `open scoped Topology BigOperators ENNReal`, `open PrimeDegreePackets`):
--
--   ```lean
--   theorem measureEntropy_le_of_bilateral_heightClip_bounds (d : ℕ)
--       (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
--       (Q : X (d+1) → ℕ) (hQ : Measurable Q)
--       (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
--       (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
--       (hlift : ∀ x y, y ∈ bilateralNameFiber ell hell Q x →
--         ∃ g ∈ matrixBall (d+1) 1, rightAction x g=y ∧
--           ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t))
--       (B : ℝ)
--       (hbound : ∀ m, observationEntropyRate μ
--         (fun z => rightAction z (diagonalOneParameter ell hell (-1))) (heightClip Q m) ≤ B) :
--       measureEntropy μ (fun z => rightAction z (diagonalOneParameter ell hell (-1))) ≤
--         ENNReal.ofReal B
--   ```
--
--   **Definitions.** The statement is written with `OAI.PrimeDegreePackets.diagonalOneParameter`, `OAI.PrimeDegreePackets.matrixBall`, `OAI.PrimeDegreePackets.measureEntropy` and `OAI.PrimeDegreePackets.observationEntropyRate` (definitions bundle `OAIQ244Duke011` of this split); `OAI.DukePrimeDegree.heightClip` (definitions bundle `OAIQ244Duke012` of this split); `OAI.DukePrimeDegree.bilateralNameFiber` (definitions bundle `OAIQ244Duke023` of this split); `OAI.PrimeDegreePackets.G`, `OAI.PrimeDegreePackets.LogCoordinates`, `OAI.PrimeDegreePackets.X`, `OAI.PrimeDegreePackets.diagonalFlow`, `OAI.PrimeDegreePackets.rightAction` and `OAI.PrimeDegreePackets.xMeasurableSpace` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proofs of `OAI.DukePrimeDegree.diagonal_entropy_zero_of_atomic_positive_roots` and `OAI.DukePrimeDegree.negative_diagonal_entropy_le_root_sum_of_small_auxiliary` of this split import it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Entropy/BilateralFiniteCodes.lean (declaration OAI.DukePrimeDegree.measureEntropy_le_of_bilateral_heightClip_bounds)

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
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke023

section

attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem measureEntropy_le_of_bilateral_heightClip_bounds (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (hlift : ∀ x y, y ∈ bilateralNameFiber ell hell Q x →
      ∃ g ∈ matrixBall (d+1) 1, rightAction x g=y ∧
        ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t))
    (B : ℝ)
    (hbound : ∀ m, observationEntropyRate μ
      (fun z => rightAction z (diagonalOneParameter ell hell (-1))) (heightClip Q m) ≤ B) :
    measureEntropy μ (fun z => rightAction z (diagonalOneParameter ell hell (-1))) ≤
      ENNReal.ofReal B := by
  sorry

end DukePrimeDegree

end

end OAI
end
