-- Prove2me | Theorems.Thm_OAI_Erdos970_Erdos970Dependency_SiegelWalfisz_moving_signed_prime_multiple_lower_jb247
-- name    : OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.moving_signed_prime_multiple_lower_jb247
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T18:46:18.199878+00:00
-- url     : https://prove2.me/theorems/aff7fbf1-f74b-4e29-b211-9e60be82e639
-- title:
--   OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.moving_signed_prime_multiple_lower_jb247: intermediate lemma from OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.moving_signed_prime_multiple_lower` of [lean/OAI/NumberTheory/Jacobsthal/Primes/WeightedPrimeMultiplePairs.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Primes/WeightedPrimeMultiplePairs.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz`, with `open scoped _root_.Erdos970`, `open _root_.Filter _root_.Finset`, `open scoped Topology`):
--
--   ```lean
--   theorem moving_signed_prime_multiple_lower_jb247 (Cs : ℝ) (hCs : 0 ≤ Cs) :
--       ∃ K : ℝ, 0 < K ∧ ∀ rho : ℝ, 1 < rho → ∀ eps : ℝ, 0 < eps → eps < 1 →
--         ∃ w₀ : ℝ, 4 ≤ w₀ ∧ ∀ w : ℝ, w₀ ≤ w → ∀ P s x y : ℝ, ∀ d : ℕ,
--           Real.exp (K*(Real.log w)^3) ≤ P → P ≤ Real.exp (rho*K*(Real.log w)^3) →
--           203/100 ≤ s → s ≤ 219/100 → P^s/2 ≤ y-x →
--           max |x| |y| ≤ 2*w^(Cs+2)*P^s → 0 < d → (d:ℝ) ≤ P^(19/20:ℝ) →
--           (1-eps)*(y-x)/((d:ℝ)*(s+1/50)*Real.log P) ≤ ((primeMultiplesIn d P x y).card:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.primeMultiplesIn` (definitions bundle `OAIQ247J002` of this split).
--
--   **Used by.** The proof of `OAI.Erdos970.ErdosStoppedArithmetic.moving_subbin_actual_pair_lower_jb247` of this split imports it.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Primes/WeightedPrimeMultiplePairs.lean (declaration OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.moving_signed_prime_multiple_lower)

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
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
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
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
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Logic.Equiv.Prod
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Tactic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Basic
import Definitions.Def_OAIQ247J002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter _root_.Finset
open scoped Topology

theorem moving_signed_prime_multiple_lower_jb247 (Cs : ℝ) (hCs : 0 ≤ Cs) :
    ∃ K : ℝ, 0 < K ∧ ∀ rho : ℝ, 1 < rho → ∀ eps : ℝ, 0 < eps → eps < 1 →
      ∃ w₀ : ℝ, 4 ≤ w₀ ∧ ∀ w : ℝ, w₀ ≤ w → ∀ P s x y : ℝ, ∀ d : ℕ,
        Real.exp (K*(Real.log w)^3) ≤ P → P ≤ Real.exp (rho*K*(Real.log w)^3) →
        203/100 ≤ s → s ≤ 219/100 → P^s/2 ≤ y-x →
        max |x| |y| ≤ 2*w^(Cs+2)*P^s → 0 < d → (d:ℝ) ≤ P^(19/20:ℝ) →
        (1-eps)*(y-x)/((d:ℝ)*(s+1/50)*Real.log P) ≤ ((primeMultiplesIn d P x y).card:ℝ) := by
  sorry

end Erdos970Dependency.SiegelWalfisz

open _root_.Filter

end Erdos970

end OAI
end
