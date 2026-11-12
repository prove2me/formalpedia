-- Prove2me | Theorems.Thm_OAI_Erdos970_ErdosStoppedArithmetic_moving_subbin_actual_pair_lower_jb247
-- name    : OAI.Erdos970.ErdosStoppedArithmetic.moving_subbin_actual_pair_lower_jb247
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T18:46:39.178603+00:00
-- url     : https://prove2.me/theorems/949c2ce8-5240-48fc-9f5e-b86be71fbb19
-- title:
--   OAI.Erdos970.ErdosStoppedArithmetic.moving_subbin_actual_pair_lower_jb247: intermediate lemma from OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Erdos970.ErdosStoppedArithmetic.moving_subbin_actual_pair_lower` of [lean/OAI/NumberTheory/Jacobsthal/Paths/TagPairBinding.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Paths/TagPairBinding.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Erdos970.ErdosStoppedArithmetic`, with `open scoped _root_.Erdos970`, `open ErdosStoppedTagSieve Erdos970Dependency.SiegelWalfisz`):
--
--   ```lean
--   theorem moving_subbin_actual_pair_lower_jb247 (Cs : ℝ) (hCs : 0 ≤ Cs) :
--       ∃ K : ℝ,0 < K ∧ ∀ rho xi : ℝ,1 < rho → 0 < xi →
--         ∃ w0 : ℝ,4 ≤ w0 ∧ ∀ w : ℝ,w0 ≤ w → ∀ P s x y R V : ℝ,
--         Real.exp (K*(Real.log w)^3) ≤ P → P ≤ Real.exp (rho*K*(Real.log w)^3) →
--         203/100 ≤ s → s ≤ 219/100 →
--         Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R →
--         xi/(16*w^(2*Cs+10)) ≤ V/R → V/R ≤ w^(-(2*Cs+10)) →
--         ∀ r : ℚ,(r.den : ℝ) ≤ w^Cs → ∀ q : ℕ,∀ a : ℕ → ℕ,
--         (∀ t ∈ smallPrimeSet P,q.Coprime t) →
--         (999/1000 : ℝ)*(r.den : ℝ)*P^s ≤ y-x →
--         max |x| |y| ≤ 2*w^(Cs+2)*P^s →
--         (39/100 : ℝ)*((intervalPrimes R V 1 0).card : ℝ)*P^s*primeProduct P ≤
--           ((admissiblePairs (intervalPrimes R V 1 0)
--             ((supportedIntegers (unalignedPrimes P r.den r.num (fun t => (a t : ℤ)))
--               ⌊P^(95/100 : ℝ)⌋₊).biUnion (fun d => primeMultiplesIn d P x y))
--             (actualTagGood P r q a)).card : ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.intervalPrimes` and `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.primeMultiplesIn` (definitions bundle `OAIQ247J002` of this split); `OAI.Erdos970.ErdosStoppedArithmetic.actualTagGood`, `OAI.Erdos970.ErdosStoppedArithmetic.admissiblePairs`, `OAI.Erdos970.ErdosStoppedTagSieve.smallPrimeSet`, `OAI.Erdos970.ErdosStoppedTagSieve.unalignedPrimes`, `OAI.Erdos970.EulerWeightedLower.supportedIntegers` and `OAI.Erdos970.ErdosPrimeInputs.MertensStrong.primeProduct` (definitions bundle `OAIQ247J003` of this split).
--
--   **Used by.** The proofs of `OAI_Erdos970_Erdos970Final_source_stopped_correction_jb247` and `OAI.Erdos970.ErdosStoppedArithmetic.actual_owner_local_comparison_jb247` of this split import it.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Paths/TagPairBinding.lean (declaration OAI.Erdos970.ErdosStoppedArithmetic.moving_subbin_actual_pair_lower)

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
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
import Mathlib.Analysis.Fourier.FourierTransformDeriv
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
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Logic.Equiv.Prod
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
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
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Tactic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Definitions.Def_OAIQ247J002
import Definitions.Def_OAIQ247J003

section

attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

namespace ErdosStoppedArithmetic
open ErdosStoppedTagSieve Erdos970Dependency.SiegelWalfisz
  Erdos970.EulerWeightedLower ErdosUnitLifts
  NumberTheoryLean.ReferenceProductsBasics ErdosPrimeInputs.MertensStrong

attribute [local instance] Classical.propDecidable

theorem moving_subbin_actual_pair_lower_jb247 (Cs : ℝ) (hCs : 0 ≤ Cs) :
    ∃ K : ℝ,0 < K ∧ ∀ rho xi : ℝ,1 < rho → 0 < xi →
      ∃ w0 : ℝ,4 ≤ w0 ∧ ∀ w : ℝ,w0 ≤ w → ∀ P s x y R V : ℝ,
      Real.exp (K*(Real.log w)^3) ≤ P → P ≤ Real.exp (rho*K*(Real.log w)^3) →
      203/100 ≤ s → s ≤ 219/100 →
      Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R →
      xi/(16*w^(2*Cs+10)) ≤ V/R → V/R ≤ w^(-(2*Cs+10)) →
      ∀ r : ℚ,(r.den : ℝ) ≤ w^Cs → ∀ q : ℕ,∀ a : ℕ → ℕ,
      (∀ t ∈ smallPrimeSet P,q.Coprime t) →
      (999/1000 : ℝ)*(r.den : ℝ)*P^s ≤ y-x →
      max |x| |y| ≤ 2*w^(Cs+2)*P^s →
      (39/100 : ℝ)*((intervalPrimes R V 1 0).card : ℝ)*P^s*primeProduct P ≤
        ((admissiblePairs (intervalPrimes R V 1 0)
          ((supportedIntegers (unalignedPrimes P r.den r.num (fun t => (a t : ℤ)))
            ⌊P^(95/100 : ℝ)⌋₊).biUnion (fun d => primeMultiplesIn d P x y))
          (actualTagGood P r q a)).card : ℝ) := by
  sorry

end ErdosStoppedArithmetic

end Erdos970

end OAI
end
