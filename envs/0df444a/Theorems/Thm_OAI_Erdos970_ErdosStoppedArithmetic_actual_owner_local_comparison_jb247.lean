-- Prove2me | Theorems.Thm_OAI_Erdos970_ErdosStoppedArithmetic_actual_owner_local_comparison_jb247
-- name    : OAI.Erdos970.ErdosStoppedArithmetic.actual_owner_local_comparison_jb247
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T18:43:28.646002+00:00
-- url     : https://prove2.me/theorems/29e23d03-d89c-4d07-b676-b78dd99c7494
-- title:
--   OAI.Erdos970.ErdosStoppedArithmetic.actual_owner_local_comparison_jb247: intermediate lemma from OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Erdos970.ErdosStoppedArithmetic.actual_owner_local_comparison` of [lean/OAI/NumberTheory/Jacobsthal/Paths/ActualOwnerLocalComparison.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Paths/ActualOwnerLocalComparison.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Erdos970.ErdosStoppedArithmetic`, with `open ErdosStoppedTagSieve ErdosCommonMInterval ErdosInverseAlignment ErdosInversePrimeBin`):
--
--   ```lean
--   theorem actual_owner_local_comparison_jb247 :
--       ∃ eta0 : ℝ,0 < eta0 ∧ eta0 ≤ 1/4 ∧ ∃ P0 : ℕ,2 ≤ P0 ∧
--         ∀ Cs : ℝ,0 ≤ Cs → ∃ K : ℝ,0 < K ∧ ∀ rho xi : ℝ,1 < rho → 0 < xi →
--         ∃ w0 : ℝ,4 ≤ w0 ∧ ∀ w : ℝ,w0 ≤ w → ∀ P : ℕ,P.Prime → P0 ≤ P →
--         ∀ R theta eta : ℝ,
--         Real.exp (K*(Real.log w)^3) ≤ (P : ℝ) → (P : ℝ) ≤ Real.exp (rho*K*(Real.log w)^3) →
--         Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R → xi/4 ≤ theta → theta ≤ 1 →
--         0 ≤ eta → eta ≤ eta0 →
--         ∀ Y q : ℕ,0 < Y → 0 < q → ∀ r : ℚ,∀ a : ℕ → ℕ,
--         (r.den : ℝ) ≤ w^Cs → |(r.num : ℝ)| ≤ (Y : ℝ)*w^(Cs+2) →
--         (∀ x ∈ Set.Icc R ((1+theta)*R),
--           203/100 ≤ lengthExponent P Y x q ∧ lengthExponent P Y x q ≤ 219/100) →
--         (∀ t ∈ smallPrimeSet (P : ℝ),q.Coprime t) →
--         (∀ p ∈ primeBin R theta,Squarefree (p*q) ∧ r.den.Coprime p ∧
--           p ∉ smallPrimeSet (P : ℝ) ∧
--           (∀ t ∈ (p*q).primeFactors,t ≠ p → aligns (fun u => (a u : ℤ)) r t) ∧
--           ∀ t ∈ (p*q).primeFactors,P ≤ t) →
--         (1-eta)*((primeBin R theta).card : ℝ) ≤
--           (((primeBin R theta).filter (aligns (fun t => (a t : ℤ)) r)).card : ℝ) →
--         ∀ reference : ℕ → ℝ,
--         (∀ p ∈ (primeBin R theta).filter (aligns (fun t => (a t : ℤ)) r),
--           reference p ≤ (33/100 : ℝ)*primeProduct (P : ℝ)*((Y : ℝ)/((p : ℝ)*q))) →
--         (1/100 : ℝ)*primeProduct (P : ℝ)*(∑ p ∈ primeBin R theta,(Y : ℝ)/((p : ℝ)*q)) ≤
--           ∑ p ∈ (primeBin R theta).filter (aligns (fun t => (a t : ℤ)) r),
--             ((modulusCount Y (smallPrimeSet (P : ℝ)) a (p*q) : ℝ)-reference p)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Erdos970.ErdosCommonMInterval.lengthExponent`, `OAI.Erdos970.ErdosInverseAlignment.aligns`, `OAI.Erdos970.ErdosInverseCounts.modulusCount`, `OAI.Erdos970.ErdosInversePrimeBin.primeBin`, `OAI.Erdos970.ErdosStoppedTagSieve.smallPrimeSet` and `OAI.Erdos970.ErdosPrimeInputs.MertensStrong.primeProduct` (definitions bundle `OAIQ247J003` of this split).
--
--   **Used by.** The proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log` of this split imports it.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Paths/ActualOwnerLocalComparison.lean (declaration OAI.Erdos970.ErdosStoppedArithmetic.actual_owner_local_comparison)

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
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Basic
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

namespace ErdosStoppedArithmetic
open ErdosStoppedTagSieve ErdosCommonMInterval ErdosInverseAlignment ErdosInversePrimeBin
  ErdosPrimeInputs.MertensStrong ErdosInverseCounts
  NumberTheoryLean.ReferenceProductsBasics

attribute [local instance] Classical.propDecidable

theorem actual_owner_local_comparison_jb247 :
    ∃ eta0 : ℝ,0 < eta0 ∧ eta0 ≤ 1/4 ∧ ∃ P0 : ℕ,2 ≤ P0 ∧
      ∀ Cs : ℝ,0 ≤ Cs → ∃ K : ℝ,0 < K ∧ ∀ rho xi : ℝ,1 < rho → 0 < xi →
      ∃ w0 : ℝ,4 ≤ w0 ∧ ∀ w : ℝ,w0 ≤ w → ∀ P : ℕ,P.Prime → P0 ≤ P →
      ∀ R theta eta : ℝ,
      Real.exp (K*(Real.log w)^3) ≤ (P : ℝ) → (P : ℝ) ≤ Real.exp (rho*K*(Real.log w)^3) →
      Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R → xi/4 ≤ theta → theta ≤ 1 →
      0 ≤ eta → eta ≤ eta0 →
      ∀ Y q : ℕ,0 < Y → 0 < q → ∀ r : ℚ,∀ a : ℕ → ℕ,
      (r.den : ℝ) ≤ w^Cs → |(r.num : ℝ)| ≤ (Y : ℝ)*w^(Cs+2) →
      (∀ x ∈ Set.Icc R ((1+theta)*R),
        203/100 ≤ lengthExponent P Y x q ∧ lengthExponent P Y x q ≤ 219/100) →
      (∀ t ∈ smallPrimeSet (P : ℝ),q.Coprime t) →
      (∀ p ∈ primeBin R theta,Squarefree (p*q) ∧ r.den.Coprime p ∧
        p ∉ smallPrimeSet (P : ℝ) ∧
        (∀ t ∈ (p*q).primeFactors,t ≠ p → aligns (fun u => (a u : ℤ)) r t) ∧
        ∀ t ∈ (p*q).primeFactors,P ≤ t) →
      (1-eta)*((primeBin R theta).card : ℝ) ≤
        (((primeBin R theta).filter (aligns (fun t => (a t : ℤ)) r)).card : ℝ) →
      ∀ reference : ℕ → ℝ,
      (∀ p ∈ (primeBin R theta).filter (aligns (fun t => (a t : ℤ)) r),
        reference p ≤ (33/100 : ℝ)*primeProduct (P : ℝ)*((Y : ℝ)/((p : ℝ)*q))) →
      (1/100 : ℝ)*primeProduct (P : ℝ)*(∑ p ∈ primeBin R theta,(Y : ℝ)/((p : ℝ)*q)) ≤
        ∑ p ∈ (primeBin R theta).filter (aligns (fun t => (a t : ℤ)) r),
          ((modulusCount Y (smallPrimeSet (P : ℝ)) a (p*q) : ℝ)-reference p) := by
  sorry

end ErdosStoppedArithmetic

end Erdos970

end OAI
end
