-- Prove2me | Theorems.Thm_OAI_Erdos970_ErdosStoppedTagSieve_tag_prime_sieve_lower_jb247
-- name    : OAI.Erdos970.ErdosStoppedTagSieve.tag_prime_sieve_lower_jb247
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T18:56:37.907006+00:00
-- url     : https://prove2.me/theorems/fc6b88a8-7cf5-4f0f-acbc-612637991974
-- title:
--   OAI.Erdos970.ErdosStoppedTagSieve.tag_prime_sieve_lower_jb247: intermediate lemma from OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Erdos970.ErdosStoppedTagSieve.tag_prime_sieve_lower` of [lean/OAI/NumberTheory/Jacobsthal/Sieve/TagPrimeSieveLower.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Sieve/TagPrimeSieveLower.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Erdos970.ErdosStoppedTagSieve`, with `open scoped _root_.Erdos970`, `open _root_.Filter`, `open scoped Topology`, `open ErdosUnitLifts Erdos970Dependency.SiegelWalfisz`):
--
--   ```lean
--   theorem tag_prime_sieve_lower_jb247 (Cs K rho xi gamma : ℝ)
--       (hCs : 0 ≤ Cs) (hK : 0 < K) (hrho : 1 < rho) (hxi : 0 < xi) (hgamma : 0 < gamma) :
--       ∃ w₀ : ℝ,3 ≤ w₀ ∧ ∀ w P R V : ℝ,w₀ ≤ w →
--         Real.exp (K*(Real.log w)^3) ≤ P → P ≤ Real.exp ((rho*K)*(Real.log w)^3) →
--         Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R →
--         xi/(16*w^(2*Cs+10)) ≤ V/R → V/R ≤ w^(-(2*Cs+10)) →
--         ∀ D : ℕ,0 < D → (D:ℝ) ≤ w^Cs → ∀ A : ℤ,A.natAbs.Coprime D →
--         ∀ residue : ℕ → ℤ,∀ q d0 ell : ℕ,∀ m : ℤ,
--         (∀ t∈smallPrimeSet P,q.Coprime t) → 0 < d0 →
--         (∀ t∈d0.primeFactors,t∈unalignedPrimes P D A residue) →
--         ell.Prime → P<(ell:ℝ) → m.natAbs=d0*ell →
--         (1-gamma)*(((intervalPrimes R V 1 0).card:ℝ)/(D:ℝ))*
--           eulerWeight (restrictedPrimes P D A residue d0) ≤
--           ((actualSurvivorPrimes P R V D A ((q:ℤ)*m) residue).card:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.intervalPrimes` (definitions bundle `OAIQ247J002` of this split); `OAI.Erdos970.ErdosStoppedTagSieve.eulerWeight`, `OAI.Erdos970.ErdosStoppedTagSieve.restrictedPrimes`, `OAI.Erdos970.ErdosStoppedTagSieve.smallPrimeSet` and `OAI.Erdos970.ErdosStoppedTagSieve.unalignedPrimes` (definitions bundle `OAIQ247J003` of this split); `OAI.Erdos970.ErdosStoppedTagSieve.actualSurvivorPrimes` (definitions bundle `OAIQ247J007` of this split).
--
--   **Used by.** The proofs of `OAI_Erdos970_ErdosStoppedArithmetic_hypothetical_subbin_lower_jb247` and `OAI.Erdos970.ErdosStoppedArithmetic.moving_subbin_actual_pair_lower_jb247` of this split import it.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Sieve/TagPrimeSieveLower.lean (declaration OAI.Erdos970.ErdosStoppedTagSieve.tag_prime_sieve_lower)

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
import Mathlib.Algebra.Ring.GeomSum
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
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
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
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
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
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Order.SuccPred.IntervalSucc
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
import Definitions.Def_OAIQ247J007

section

attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

namespace ErdosStoppedTagSieve

open _root_.Filter
open scoped Topology
open ErdosUnitLifts Erdos970Dependency.SiegelWalfisz

theorem tag_prime_sieve_lower_jb247 (Cs K rho xi gamma : ℝ)
    (hCs : 0 ≤ Cs) (hK : 0 < K) (hrho : 1 < rho) (hxi : 0 < xi) (hgamma : 0 < gamma) :
    ∃ w₀ : ℝ,3 ≤ w₀ ∧ ∀ w P R V : ℝ,w₀ ≤ w →
      Real.exp (K*(Real.log w)^3) ≤ P → P ≤ Real.exp ((rho*K)*(Real.log w)^3) →
      Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R →
      xi/(16*w^(2*Cs+10)) ≤ V/R → V/R ≤ w^(-(2*Cs+10)) →
      ∀ D : ℕ,0 < D → (D:ℝ) ≤ w^Cs → ∀ A : ℤ,A.natAbs.Coprime D →
      ∀ residue : ℕ → ℤ,∀ q d0 ell : ℕ,∀ m : ℤ,
      (∀ t∈smallPrimeSet P,q.Coprime t) → 0 < d0 →
      (∀ t∈d0.primeFactors,t∈unalignedPrimes P D A residue) →
      ell.Prime → P<(ell:ℝ) → m.natAbs=d0*ell →
      (1-gamma)*(((intervalPrimes R V 1 0).card:ℝ)/(D:ℝ))*
        eulerWeight (restrictedPrimes P D A residue d0) ≤
        ((actualSurvivorPrimes P R V D A ((q:ℤ)*m) residue).card:ℝ) := by
  sorry

end ErdosStoppedTagSieve

end Erdos970

end OAI
end
