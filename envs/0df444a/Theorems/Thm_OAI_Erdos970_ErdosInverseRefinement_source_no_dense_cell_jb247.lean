-- Prove2me | Theorems.Thm_OAI_Erdos970_ErdosInverseRefinement_source_no_dense_cell_jb247
-- name    : OAI.Erdos970.ErdosInverseRefinement.source_no_dense_cell_jb247
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T18:43:22.37521+00:00
-- url     : https://prove2.me/theorems/49d38735-21af-4630-9683-15bdf38317ce
-- title:
--   OAI.Erdos970.ErdosInverseRefinement.source_no_dense_cell_jb247: intermediate lemma from OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Erdos970.ErdosInverseRefinement.source_no_dense_cell` of [lean/OAI/NumberTheory/Jacobsthal/Partitions/SourceDenseCellContradiction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Partitions/SourceDenseCellContradiction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Erdos970.ErdosInverseRefinement`, with `open _root_.Filter`, `open scoped Topology`, `open NumberTheoryLean ErdosInverseCells ErdosInverseSampling ErdosInverseSampleCost`):
--
--   ```lean
--   theorem source_no_dense_cell_jb247 (Clen Cparent aStar K alpha delta beta : ℝ) (h : ℕ)
--       (hClen : 0 ≤ Clen) (hCparent : 0 ≤ Cparent) (ha : 0 < aStar) (ha1 : aStar ≤ 1)
--       (hK : 0 ≤ K) (halpha : 0 < alpha) (hd : 0 < delta) (hb : 0 < beta) (hb1 : beta ≤ 1)
--       (hh : 12 < aStar*(h : ℝ)/2) :
--       ∃ xi0 : ℝ,0 < xi0 ∧ xi0 ≤ 1 ∧ ∀ xi : ℝ,0 < xi → xi ≤ xi0 →
--         ∀ᶠ z : ℝ in atTop,∀ R thetaP U thetaU Qplus S : ℝ,
--           ∀ (C : Finset ℕ) (q0 : ℕ) (b0 : ℤ) (a : ℕ → ℕ),
--           z^alpha ≤ R → R ≤ z^((1 : ℝ)/100) → sourceW z ≤ U → U ≤ (sourceW z)^K →
--           xi/4 ≤ thetaP → thetaP ≤ xi → xi/4 ≤ thetaU → thetaU ≤ xi →
--           q0 ∈ C → 0 < q0 →
--           S/(q0 : ℝ) ≤ (1+thetaP)^(Clen*Real.log (sourceB z)) →
--           (∀ q ∈ C,Squarefree q ∧ (q : ℝ) ≤ S) →
--           (∀ q ∈ C,(q : ℝ) ≤ Qplus ∧ Qplus ≤ (1+xi)*(q : ℝ)) →
--           (∀ p ∈ primeBin R thetaP,∀ u ∈ primeBin U thetaU,p.Coprime u) →
--           (∀ q ∈ C,∀ p ∈ primeBin R thetaP,q.Coprime p) →
--           (∀ q ∈ C,∀ u ∈ primeBin U thetaU,q.Coprime u) →
--           (∀ q ∈ C,∀ p ∈ primeBin R thetaP,∀ t : ℕ,t.Prime →
--             (t : ℝ) ≤ sourceW z → (p*q).Coprime t) →
--           (∀ q ∈ C,∀ p ∈ primeBin R thetaP,∀ u ∈ primeBin U thetaU,
--             3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*q*u))/Real.log (sourceW z)) →
--           (∀ p ∈ primeBin R thetaP,
--             Real.logb (sourceW z) ((sourceY z : ℝ)/((p : ℝ)*q0)) ≤ Cparent) →
--           (∀ q ∈ C,Int.ModEq (smallModulus (sourceW z) : ℤ) (q : ℤ) (q0 : ℤ) ∧
--             Int.ModEq (smallModulus (sourceW z) : ℤ) (cofactorHit q a : ℤ) b0) →
--           S/sourceZ z ≤ (C.card : ℝ) →
--           let P := primeBin R thetaP
--           let Uset := primeBin U thetaU
--           let witness := actualWitness (sourceY z) (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊) a delta
--             (SmallSieveFinite.smallEuler ⌊sourceW z⌋₊) P S R (sourceZ z) (sampleGamma beta h/32)
--           beta*((P.product C).card : ℝ)*(Uset.card : ℝ) ≤
--             ((witnessPairs (P.product C) Uset witness).card : ℝ) → False
--   ```
--
--   **Definitions.** The statement is written with `OAI.Erdos970.ErdosInverseBoxHeight.sourceB`, `OAI.Erdos970.ErdosInverseBoxHeight.sourceW`, `OAI.Erdos970.ErdosInverseBoxHeight.sourceY`, `OAI.Erdos970.ErdosInverseBoxHeight.sourceZ`, `OAI.Erdos970.ErdosInverseCells.cofactorHit`, `OAI.Erdos970.ErdosInverseEuler.smallModulus`, `OAI.Erdos970.ErdosInversePrimeBin.primeBin`, `OAI.Erdos970.ErdosInverseSampleCost.actualWitness`, `OAI.Erdos970.ErdosInverseSampleCost.sampleGamma`, `OAI.Erdos970.ErdosInverseSampling.witnessPairs`, `OAI.Erdos970.NumberTheoryLean.LargePrimeDeletion.cutoffPrimes` and `OAI.Erdos970.NumberTheoryLean.SmallSieveFinite.smallEuler` (definitions bundle `OAIQ247J003` of this split).
--
--   **Used by.** The proof of `OAI.Erdos970.ErdosInverseBoxApplication.actual_source_inverse_jb247` of this split imports it.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Partitions/SourceDenseCellContradiction.lean (declaration OAI.Erdos970.ErdosInverseRefinement.source_no_dense_cell)

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.GroupTheory.Index
import Mathlib.Logic.Equiv.Prod
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UrysohnsLemma
import Definitions.Def_OAIQ247J003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseRefinement
open NumberTheoryLean ErdosInverseCells ErdosInverseSampling ErdosInverseSampleCost
  ErdosInverseEuler ErdosInverseStructured ErdosInverseBoxHeight ErdosInversePrimeBin

theorem source_no_dense_cell_jb247 (Clen Cparent aStar K alpha delta beta : ℝ) (h : ℕ)
    (hClen : 0 ≤ Clen) (hCparent : 0 ≤ Cparent) (ha : 0 < aStar) (ha1 : aStar ≤ 1)
    (hK : 0 ≤ K) (halpha : 0 < alpha) (hd : 0 < delta) (hb : 0 < beta) (hb1 : beta ≤ 1)
    (hh : 12 < aStar*(h : ℝ)/2) :
    ∃ xi0 : ℝ,0 < xi0 ∧ xi0 ≤ 1 ∧ ∀ xi : ℝ,0 < xi → xi ≤ xi0 →
      ∀ᶠ z : ℝ in atTop,∀ R thetaP U thetaU Qplus S : ℝ,
        ∀ (C : Finset ℕ) (q0 : ℕ) (b0 : ℤ) (a : ℕ → ℕ),
        z^alpha ≤ R → R ≤ z^((1 : ℝ)/100) → sourceW z ≤ U → U ≤ (sourceW z)^K →
        xi/4 ≤ thetaP → thetaP ≤ xi → xi/4 ≤ thetaU → thetaU ≤ xi →
        q0 ∈ C → 0 < q0 →
        S/(q0 : ℝ) ≤ (1+thetaP)^(Clen*Real.log (sourceB z)) →
        (∀ q ∈ C,Squarefree q ∧ (q : ℝ) ≤ S) →
        (∀ q ∈ C,(q : ℝ) ≤ Qplus ∧ Qplus ≤ (1+xi)*(q : ℝ)) →
        (∀ p ∈ primeBin R thetaP,∀ u ∈ primeBin U thetaU,p.Coprime u) →
        (∀ q ∈ C,∀ p ∈ primeBin R thetaP,q.Coprime p) →
        (∀ q ∈ C,∀ u ∈ primeBin U thetaU,q.Coprime u) →
        (∀ q ∈ C,∀ p ∈ primeBin R thetaP,∀ t : ℕ,t.Prime →
          (t : ℝ) ≤ sourceW z → (p*q).Coprime t) →
        (∀ q ∈ C,∀ p ∈ primeBin R thetaP,∀ u ∈ primeBin U thetaU,
          3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*q*u))/Real.log (sourceW z)) →
        (∀ p ∈ primeBin R thetaP,
          Real.logb (sourceW z) ((sourceY z : ℝ)/((p : ℝ)*q0)) ≤ Cparent) →
        (∀ q ∈ C,Int.ModEq (smallModulus (sourceW z) : ℤ) (q : ℤ) (q0 : ℤ) ∧
          Int.ModEq (smallModulus (sourceW z) : ℤ) (cofactorHit q a : ℤ) b0) →
        S/sourceZ z ≤ (C.card : ℝ) →
        let P := primeBin R thetaP
        let Uset := primeBin U thetaU
        let witness := actualWitness (sourceY z) (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊) a delta
          (SmallSieveFinite.smallEuler ⌊sourceW z⌋₊) P S R (sourceZ z) (sampleGamma beta h/32)
        beta*((P.product C).card : ℝ)*(Uset.card : ℝ) ≤
          ((witnessPairs (P.product C) Uset witness).card : ℝ) → False := by
  sorry

end ErdosInverseRefinement

end

end Erdos970

end OAI
end
