-- Prove2me | Theorems.Thm_Helfgott_moebius_reciprocal_high_of_prime_errors_and_tail_mertens
-- name    : Helfgott.moebius_reciprocal_high_of_prime_errors_and_tail_mertens
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T00:45:32.880912+00:00
-- url     : https://prove2.me/theorems/4fa4a870-d224-42f2-bad4-3274e831197e
-- title:
--   High reciprocal Mobius decay from prime-error envelopes and a tail Mertens bound
-- statement:
--   Let $M(u)=\sum_{n\le\lfloor u\rfloor}\mu(n)$ and $A_C(u)=\sum_{k\le\lfloor u\rfloor}((\Lambda*\Lambda)(k)-\Lambda(k)\log k+C)$, where $*$ denotes Dirichlet convolution. Suppose $C\in\mathbb R$, $|C|\le2$, and
--   $$|A_C(u)|\le0.031u\quad(21\cdot10^9\le u<10^{16}),\qquad |A_C(u)|\le0.0065u\quad(u\ge10^{16}).$$
--   Suppose also that $|M(U)|\le U/4345$ for every integer $U\ge10^{16}$. Then every real $x\ge10^{28}$ satisfies
--   $$\left|\sum_{n\le\lfloor x\rfloor}\frac{\mu(n)}{n}\right|\le\frac{0.03}{\log x}.$$
--   The finite convolution moment and all weight-removal and initial-integral corrections are proved within this conversion. The two prime-error envelopes and the coarse Mertens tail remain explicit assumptions. No Mertens hypothesis below $10^{16}$ or finite Hurst computation is required.
-- source:
--   Independent corrected high-range Ramare-style conversion. Related to O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Written by Codex.

import Theorems.Thm_Helfgott_moebius_log_squared_two_range_hyperbola_bound
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Theorems.Thm_Helfgott_centered_prime_finite_moment_twenty_one_billion
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

theorem moebius_reciprocal_high_of_prime_errors_and_tail_mertens 
    (x C : ℝ) (hx : 10000000000000000000000000000 ≤ x) (hC : |C| ≤ 2)
    (hRhigh : ∀ u : ℝ, 10000000000000000 ≤ u →
      |∑ k ∈ Icc 1 ⌊u⌋₊,
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| ≤
          (65 / 10000) * u)
    (hRmiddle : ∀ u : ℝ, 21000000000 ≤ u → u < 10000000000000000 →
      |∑ k ∈ Icc 1 ⌊u⌋₊,
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| ≤
          (31 / 1000) * u)
    (hM : ∀ u : ℕ, 10000000000000000 ≤ u →
      |∑ d ∈ Icc 1 u, ((moebius d : ℤ) : ℝ)| ≤ (u : ℝ) / 4345) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, ((moebius n : ℤ) : ℝ) / (n : ℝ)| ≤
      (3 / 100) / Real.log x := by sorry

end Helfgott
