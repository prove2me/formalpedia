-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_exists_cover_stationary_wholeFutureKernel
-- name    : OAI.DukePrimeDegree.exists_cover_stationary_wholeFutureKernel
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:34:36.449127+00:00
-- url     : https://prove2.me/theorems/b6105925-508c-46b2-9492-8b3582978c2d
-- title:
--   OAI.DukePrimeDegree.exists_cover_stationary_wholeFutureKernel: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.exists_cover_stationary_wholeFutureKernel` of [lean/OAI/NumberTheory/DukePrimeDegree/Entropy/StationaryCoverObservation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Entropy/StationaryCoverObservation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology ENNReal`, `open PrimeDegreePackets`):
--
--   ```lean
--   theorem exists_cover_stationary_wholeFutureKernel (d : ℕ)
--       (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
--       (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
--       (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
--       [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
--       {ε : ℝ} (hε : 0 < ε) :
--       ∃ (H Q : X (d+1) → ℕ) (κ : Kernel (X (d+1)) (X (d+1))),
--         Measurable H ∧ Measurable Q ∧ IsMarkovKernel κ ∧
--         (∀ m, IsCompact {x | H x ≤ m}) ∧
--         (∀ m, (Q '' {x | H x ≤ m}).Finite) ∧
--         (∀ N, observationEntropyRate μ
--           (fun x => rightAction x (diagonalOneParameter ell hell (-1))) (heightClip H N) < ε) ∧
--         (∀ x y,
--           (∀ k : ℕ,
--             Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
--             Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
--           (∀ k : ℕ,
--             Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] y) =
--             Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] x)) →
--           ∃ g ∈ matrixBall (d+1) 1, rightAction x g=y ∧
--             ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t)) ∧
--         μ.bind κ = μ ∧
--         (∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x) ∧
--         (∀ᵐ x ∂μ,
--           let c := completeRootChain (d+1)
--           κ x = ((anchorNormalize (c.remainingTimeProduct
--             (by intro p hp; simp at hp) (completeRootChain_final (d+1)) μ x)
--             (c.remainingFutureAtom ell hell Q 1 x)).restrict
--             (c.remainingFutureAtom ell hell Q 1 x)).map
--             (fun u => rightAction x (c.word u))) ∧
--         (∀ᵐ x ∂μ,
--           let c := completeRootChain (d+1)
--           0 < c.remainingTimeProduct (by intro p hp; simp at hp)
--             (completeRootChain_final (d+1)) μ x (c.remainingFutureAtom ell hell Q 0 x) ∧
--           c.remainingTimeProduct (by intro p hp; simp at hp)
--             (completeRootChain_final (d+1)) μ x (c.remainingFutureAtom ell hell Q 0 x) ≤ 1) ∧
--         (∀ x, H (rightAction x (diagonalOneParameter ell hell (-1))) ≤ H x+1 ∧
--           H x ≤ H (rightAction x (diagonalOneParameter ell hell (-1)))+1) ∧
--         (∀ x y, Q y=Q x → H y=H x) ∧
--         (∀ x y, (∀ k : ℕ,
--           Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
--           Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
--           ∃ g : G (d+1), rightAction x g=y ∧
--             ∀ i j, ell j < ell i → g.val i j = 0) ∧
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
--   **Definitions.** The statement is written with `OAI.DukePrimeDegree.EliminationChain`, `OAI.DukePrimeDegree.UpperRootTime`, `OAI.DukePrimeDegree.allPositiveRoots`, `OAI.DukePrimeDegree.completeRootChain`, `OAI.DukePrimeDegree.completeRootChain_final`, `OAI.PrimeDegreePackets.anchorNormalize`, `OAI.PrimeDegreePackets.diagonalLogAction`, `OAI.PrimeDegreePackets.diagonalOneParameter`, `OAI.PrimeDegreePackets.matrixBall`, `OAI.PrimeDegreePackets.observationEntropyRate`, `OAI.DukePrimeDegree.EliminationChain.Time`, `OAI.DukePrimeDegree.EliminationChain.time_measurableSpace` and `OAI.DukePrimeDegree.EliminationChain.word` (definitions bundle `OAIQ244Duke011` of this split); `OAI.DukePrimeDegree.heightClip` (definitions bundle `OAIQ244Duke012` of this split); `OAI.DukePrimeDegree.EliminationChain.remainingFutureAtom` and `OAI.DukePrimeDegree.EliminationChain.remainingTimeProduct` (definitions bundle `OAIQ244Duke022` of this split); `OAI.PrimeDegreePackets.G`, `OAI.PrimeDegreePackets.LogCoordinates`, `OAI.PrimeDegreePackets.X`, `OAI.PrimeDegreePackets.integralGroup`, `OAI.PrimeDegreePackets.rightAction` and `OAI.PrimeDegreePackets.xMeasurableSpace` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proof of `OAI.DukePrimeDegree.positive_root_sum_le_diagonal_entropy` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Entropy/StationaryCoverObservation.lean (declaration OAI.DukePrimeDegree.exists_cover_stationary_wholeFutureKernel)

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

attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_cover_stationary_wholeFutureKernel (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (H Q : X (d+1) → ℕ) (κ : Kernel (X (d+1)) (X (d+1))),
      Measurable H ∧ Measurable Q ∧ IsMarkovKernel κ ∧
      (∀ m, IsCompact {x | H x ≤ m}) ∧
      (∀ m, (Q '' {x | H x ≤ m}).Finite) ∧
      (∀ N, observationEntropyRate μ
        (fun x => rightAction x (diagonalOneParameter ell hell (-1))) (heightClip H N) < ε) ∧
      (∀ x y,
        (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] y) =
          Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] x)) →
        ∃ g ∈ matrixBall (d+1) 1, rightAction x g=y ∧
          ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t)) ∧
      μ.bind κ = μ ∧
      (∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x) ∧
      (∀ᵐ x ∂μ,
        let c := completeRootChain (d+1)
        κ x = ((anchorNormalize (c.remainingTimeProduct
          (by intro p hp; simp at hp) (completeRootChain_final (d+1)) μ x)
          (c.remainingFutureAtom ell hell Q 1 x)).restrict
          (c.remainingFutureAtom ell hell Q 1 x)).map
          (fun u => rightAction x (c.word u))) ∧
      (∀ᵐ x ∂μ,
        let c := completeRootChain (d+1)
        0 < c.remainingTimeProduct (by intro p hp; simp at hp)
          (completeRootChain_final (d+1)) μ x (c.remainingFutureAtom ell hell Q 0 x) ∧
        c.remainingTimeProduct (by intro p hp; simp at hp)
          (completeRootChain_final (d+1)) μ x (c.remainingFutureAtom ell hell Q 0 x) ≤ 1) ∧
      (∀ x, H (rightAction x (diagonalOneParameter ell hell (-1))) ≤ H x+1 ∧
        H x ≤ H (rightAction x (diagonalOneParameter ell hell (-1)))+1) ∧
      (∀ x y, Q y=Q x → H y=H x) ∧
      (∀ x y, (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        ∃ g : G (d+1), rightAction x g=y ∧
          ∀ i j, ell j < ell i → g.val i j = 0) ∧
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
