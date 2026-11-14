-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_exists_sparse_upperRoot_comparison
-- name    : OAI.DukePrimeDegree.exists_sparse_upperRoot_comparison
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:36:29.439+00:00
-- url     : https://prove2.me/theorems/2116f64f-4d5e-4168-831f-e8bcb2c123ca
-- title:
--   OAI.DukePrimeDegree.exists_sparse_upperRoot_comparison: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.exists_sparse_upperRoot_comparison` of [lean/OAI/NumberTheory/DukePrimeDegree/Geometry/SparseUpperRootComparison.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Geometry/SparseUpperRootComparison.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree`, with `open Set MeasureTheory`, `open scoped Topology BigOperators`, `open PrimeDegreePackets`):
--
--   ```lean
--   theorem exists_sparse_upperRoot_comparison {n : ℕ}
--       (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (hord : StrictMono ell)
--       (μ : Measure (X n)) [IsProbabilityMeasure μ]
--       (hT : MeasurePreserving (fun x => rightAction x (diagonalOneParameter ell hell (-1))) μ μ)
--       (E : Set (X n)) (hE : MeasurableSet E)
--       (hfree : ∀ x ∈ E, ∀ k : ℕ, 0 < k →
--         (fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x ≠ x)
--       (H : X n → ℕ) (hH : Measurable H)
--       (r : ℕ → ℝ) (hr : ∀ m, 0 < r m) (hr1 : ∀ m, r m ≤ 1) (hanti : Antitone r)
--       (hinj : ∀ x, Set.InjOn (fun g => rightAction x g) (matrixBall n (r (H x))))
--       (Q : X n → ℕ)
--       (hlift : ∀ x y, (∀ k : ℕ,
--         Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y)=
--         Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
--         ∃ g ∈ matrixBall n (r (H x)), rightAction x g=y ∧
--           (∀ i j, ell j < ell i → g.val i j=0) ∧
--           ∀ k : ℕ, diagonalOneParameter ell hell (k:ℝ)*g*
--             diagonalOneParameter ell hell (-(k:ℝ)) ∈ matrixBall n
--               (r (H ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x))))
--       {ε : ℝ} (hε : 0 < ε) :
--       ∃ R : X n → ℕ, Measurable R ∧
--         Summable (fun i => Real.negMulLog (μ.real {x | R x=i})) ∧
--         (∑' i, Real.negMulLog (μ.real {x | R x=i})) < ε ∧
--         ∀ᵐ x ∂μ, x ∈ E → ∀ y,
--           (∀ k : ℕ,
--             Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y)=
--             Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
--           (∀ k : ℕ,
--             R ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] y)=
--             R ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
--           ∃ u : UpperRootTime n, rightAction x ((completeRootChain n).word u)=y
--   ```
--
--   **Definitions.** The statement is written with `OAI.DukePrimeDegree.UpperRootTime`, `OAI.DukePrimeDegree.completeRootChain`, `OAI.PrimeDegreePackets.diagonalOneParameter`, `OAI.PrimeDegreePackets.matrixBall` and `OAI.DukePrimeDegree.EliminationChain.word` (definitions bundle `OAIQ244Duke011` of this split); `OAI.PrimeDegreePackets.G`, `OAI.PrimeDegreePackets.X`, `OAI.PrimeDegreePackets.rightAction` and `OAI.PrimeDegreePackets.xMeasurableSpace` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proof of `OAI.DukePrimeDegree.eklPrimeInput_unconditional` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Geometry/SparseUpperRootComparison.lean (declaration OAI.DukePrimeDegree.exists_sparse_upperRoot_comparison)

import Mathlib
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Pairing
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke011

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_sparse_upperRoot_comparison {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (hord : StrictMono ell)
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving (fun x => rightAction x (diagonalOneParameter ell hell (-1))) μ μ)
    (E : Set (X n)) (hE : MeasurableSet E)
    (hfree : ∀ x ∈ E, ∀ k : ℕ, 0 < k →
      (fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x ≠ x)
    (H : X n → ℕ) (hH : Measurable H)
    (r : ℕ → ℝ) (hr : ∀ m, 0 < r m) (hr1 : ∀ m, r m ≤ 1) (hanti : Antitone r)
    (hinj : ∀ x, Set.InjOn (fun g => rightAction x g) (matrixBall n (r (H x))))
    (Q : X n → ℕ)
    (hlift : ∀ x y, (∀ k : ℕ,
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y)=
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
      ∃ g ∈ matrixBall n (r (H x)), rightAction x g=y ∧
        (∀ i j, ell j < ell i → g.val i j=0) ∧
        ∀ k : ℕ, diagonalOneParameter ell hell (k:ℝ)*g*
          diagonalOneParameter ell hell (-(k:ℝ)) ∈ matrixBall n
            (r (H ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x))))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : X n → ℕ, Measurable R ∧
      Summable (fun i => Real.negMulLog (μ.real {x | R x=i})) ∧
      (∑' i, Real.negMulLog (μ.real {x | R x=i})) < ε ∧
      ∀ᵐ x ∂μ, x ∈ E → ∀ y,
        (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y)=
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        (∀ k : ℕ,
          R ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] y)=
          R ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
        ∃ u : UpperRootTime n, rightAction x ((completeRootChain n).word u)=y := by
  sorry

end DukePrimeDegree

end

end OAI
end
