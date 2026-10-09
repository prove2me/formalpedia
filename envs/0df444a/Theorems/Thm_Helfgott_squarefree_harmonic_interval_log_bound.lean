-- Prove2me | Theorems.Thm_Helfgott_squarefree_harmonic_interval_log_bound
-- name    : Helfgott.squarefree_harmonic_interval_log_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T00:08:27.828589+00:00
-- url     : https://prove2.me/theorems/a44f87b9-e6b1-4505-970f-f471fede2ab9
-- title:
--   Squarefree harmonic interval bound with explicit floor error
-- statement:
--   For every real $0<a\le x$,
--   $$\sum_{\lfloor a\rfloor<n\le\lfloor x\rfloor}\frac{\mu(n)^2}{n}\le\frac6{\pi^2}\log(x/a)+\frac9{\sqrt a}+\frac6{\pi^2a}.$$
--   The estimate is unconditional and retains arbitrary real floor endpoints. It supplies the harmonic mass of a separate range of divisors when distinct prime-error envelopes are used in the centered Mobius hyperbola argument.
-- source:
--   Independent explicit Abel-summation consequence of the proved squarefree counting estimate. In the framework of O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Written by Codex.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Data.Rat.BigOperators
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

theorem squarefree_harmonic_interval_log_bound  (a x : ℝ) (ha : 0 < a) (hax : a ≤ x) :
    (∑ n ∈ Ioc ⌊a⌋₊ ⌊x⌋₊, ((moebius n : ℤ) : ℝ) ^ 2 / (n : ℝ)) ≤
      (6 / Real.pi ^ 2) * Real.log (x / a) +
        9 / Real.sqrt a + (6 / Real.pi ^ 2) / a := by sorry

end Helfgott
