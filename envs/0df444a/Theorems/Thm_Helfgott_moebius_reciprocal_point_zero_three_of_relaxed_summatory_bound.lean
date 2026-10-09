-- Prove2me | Theorems.Thm_Helfgott_moebius_reciprocal_point_zero_three_of_relaxed_summatory_bound
-- name    : Helfgott.moebius_reciprocal_point_zero_three_of_relaxed_summatory_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:49:16.399314+00:00
-- url     : https://prove2.me/theorems/3af27690-485e-45c4-b860-f3022caa3519
-- title:
--   Reciprocal Mobius decay from the weaker summatory rate 0.014/log
-- statement:
--   For every real $x\ge1200000$, suppose
--   $$|M(t)|\le0.014\,t/\log t\quad(1078853\le t\le x),\qquad
--   \int_1^{1078853}|M(t)|/t\,dt\le303,$$
--   where $M(t)=\sum_{1\le n\le\lfloor t\rfloor}\mu(n)$. Then
--   $$\left|\sum_{1\le n\le\lfloor x\rfloor}\mu(n)/n\right|\le0.03/\log x.$$
--   The conclusion and cutoff are unchanged from the required explicit reciprocal estimate, while the analytic input is weaker than the rate $(0.013\log t-0.118)t/\log^2t$. The summatory hypothesis remains an explicit subsequent obligation.
-- source:
--   Independent quantitative application of the El Marraki conversion, in the framework of O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Written by Codex.

import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

theorem moebius_reciprocal_point_zero_three_of_relaxed_summatory_bound  (x : ℝ)
    (hx : 1200000 ≤ x)
    (hM : ∀ t ∈ Set.Icc (1078853 : ℝ) x,
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| ≤
        (7 / 500) * t / Real.log t)
    (hinitial : (∫ t in (1 : ℝ)..(1078853 : ℝ),
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) ≤ 303) :
    |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)| ≤
      (3 / 100) / Real.log x := by sorry

end Helfgott
