-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_negative_diagonal_entropy_le_root_sum_of_small_auxiliary
-- name    : OAI.DukePrimeDegree.negative_diagonal_entropy_le_root_sum_of_small_auxiliary
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:39:33.255714+00:00
-- url     : https://prove2.me/theorems/cb854367-0f84-4556-93c2-835a8930e1ae
-- title:
--   OAI.DukePrimeDegree.negative_diagonal_entropy_le_root_sum_of_small_auxiliary: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.negative_diagonal_entropy_le_root_sum_of_small_auxiliary` of [lean/OAI/NumberTheory/DukePrimeDegree/Entropy/RegularRootEntropyUpper.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Entropy/RegularRootEntropyUpper.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology BigOperators ENNReal`, `open PrimeDegreePackets`):
--
--   ```lean
--   theorem negative_diagonal_entropy_le_root_sum_of_small_auxiliary (d : ℕ)
--       (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
--       (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
--       [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
--       (Q : X (d+1) → ℕ) (hQ : Measurable Q)
--       (hbound : ∀ᵐ x ∂μ, ∀ v : UpperRootTime (d+1),
--         (∀ k : ℕ,
--           Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k]
--             (rightAction x ((completeRootChain (d+1)).word v))) =
--           Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
--         v ∈ (completeRootChain (d+1)).cube 1)
--       (hgood : ∀ᵐ x ∂μ, ∀ᶠ v in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
--         Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k]
--           (rightAction x ((completeRootChain (d+1)).word v))) =
--         Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x))
--       (hfinite : UniformFinitePredecessors
--         (fun z => rightAction z (diagonalOneParameter ell hell (-1))) Q)
--       (hneutral : ∀ x y, y ∈ bilateralNameFiber ell hell Q x →
--         ∃ g ∈ matrixBall (d+1) 1, rightAction x g=y ∧
--           ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t))
--       (haux : ∀ ε : ℝ, 0 < ε →
--         ∃ R : X (d+1) → ℕ, Measurable R ∧
--           Summable (fun n => Real.negMulLog (μ.real {x | R x=n})) ∧
--           (∑' n, Real.negMulLog (μ.real {x | R x=n})) < ε ∧
--           ∃ E : Set (X (d+1)), (∀ᵐ x ∂μ, x ∈ E) ∧
--             ∀ x ∈ E, ∀ y ∈ E,
--               (∀ k : ℕ,
--                 Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] y) =
--                 Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
--               (∀ k : ℕ,
--                 R ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] y) =
--                 R ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
--               ∃ u : UpperRootTime (d+1),
--                 rightAction x ((completeRootChain (d+1)).word u)=y) :
--       measureEntropy μ (fun z => rightAction z (diagonalOneParameter ell hell (-1))) ≤
--         ENNReal.ofReal (∑ p : allPositiveRoots (d+1),
--           (ell p.val.2-ell p.val.1)*canonicalRootCoefficient d μ p.val.1 p.val.2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DukePrimeDegree.UpperRootTime`, `OAI.DukePrimeDegree.allPositiveRoots`, `OAI.DukePrimeDegree.completeRootChain`, `OAI.PrimeDegreePackets.diagonalLogAction`, `OAI.PrimeDegreePackets.diagonalOneParameter`, `OAI.PrimeDegreePackets.matrixBall`, `OAI.PrimeDegreePackets.measureEntropy`, `OAI.DukePrimeDegree.EliminationChain.Time`, `OAI.DukePrimeDegree.EliminationChain.cube`, `OAI.DukePrimeDegree.EliminationChain.timeTopology`, `OAI.DukePrimeDegree.EliminationChain.word` and `OAI.DukePrimeDegree.EliminationChain.zeroTime` (definitions bundle `OAIQ244Duke011` of this split); `OAI.DukePrimeDegree.UniformFinitePredecessors` (definitions bundle `OAIQ244Duke012` of this split); `OAI.DukePrimeDegree.canonicalRootCoefficient` (definitions bundle `OAIQ244Duke022` of this split); `OAI.DukePrimeDegree.bilateralNameFiber` (definitions bundle `OAIQ244Duke023` of this split); `OAI.PrimeDegreePackets.G`, `OAI.PrimeDegreePackets.LogCoordinates`, `OAI.PrimeDegreePackets.X`, `OAI.PrimeDegreePackets.rightAction` and `OAI.PrimeDegreePackets.xMeasurableSpace` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proof of `OAI.DukePrimeDegree.eklPrimeInput_unconditional` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Entropy/RegularRootEntropyUpper.lean (declaration OAI.DukePrimeDegree.negative_diagonal_entropy_le_root_sum_of_small_auxiliary)

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
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke022
import Definitions.Def_OAIQ244Duke023

section

attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

theorem negative_diagonal_entropy_le_root_sum_of_small_auxiliary (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (hbound : ∀ᵐ x ∂μ, ∀ v : UpperRootTime (d+1),
      (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k]
          (rightAction x ((completeRootChain (d+1)).word v))) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
      v ∈ (completeRootChain (d+1)).cube 1)
    (hgood : ∀ᵐ x ∂μ, ∀ᶠ v in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k]
        (rightAction x ((completeRootChain (d+1)).word v))) =
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x))
    (hfinite : UniformFinitePredecessors
      (fun z => rightAction z (diagonalOneParameter ell hell (-1))) Q)
    (hneutral : ∀ x y, y ∈ bilateralNameFiber ell hell Q x →
      ∃ g ∈ matrixBall (d+1) 1, rightAction x g=y ∧
        ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t))
    (haux : ∀ ε : ℝ, 0 < ε →
      ∃ R : X (d+1) → ℕ, Measurable R ∧
        Summable (fun n => Real.negMulLog (μ.real {x | R x=n})) ∧
        (∑' n, Real.negMulLog (μ.real {x | R x=n})) < ε ∧
        ∃ E : Set (X (d+1)), (∀ᵐ x ∂μ, x ∈ E) ∧
          ∀ x ∈ E, ∀ y ∈ E,
            (∀ k : ℕ,
              Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] y) =
              Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
            (∀ k : ℕ,
              R ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] y) =
              R ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
            ∃ u : UpperRootTime (d+1),
              rightAction x ((completeRootChain (d+1)).word u)=y) :
    measureEntropy μ (fun z => rightAction z (diagonalOneParameter ell hell (-1))) ≤
      ENNReal.ofReal (∑ p : allPositiveRoots (d+1),
        (ell p.val.2-ell p.val.1)*canonicalRootCoefficient d μ p.val.1 p.val.2) := by
  sorry

end DukePrimeDegree

end

end OAI
end
