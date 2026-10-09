-- Prove2me | Theorems.Thm_Helfgott_summatory_explicit_log_decay_of_log_squared
-- name    : Helfgott.summatory_explicit_log_decay_of_log_squared
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:55:16.599421+00:00
-- url     : https://prove2.me/theorems/3861b0b8-fb2a-4a7c-a927-53a21e3e2804
-- title:
--   Quantitative log-weight removal for the explicit summatory Mobius estimate
-- statement:
--   Let $(c_n)$ be a real sequence and define $M(t)=\sum_{n\le\lfloor t\rfloor}c_n$ and $W(t)=\sum_{n\le\lfloor t\rfloor}c_n\log^2 n$. Let $1<a\le x$. Suppose $|W(t)|\le t(0.013\log t-0.144)$ for every $a\le t\le x$ and $$\left|M(a)-\frac{W(a)}{\log^2a}\right|\le\frac{0.026a}{\log^2a}.$$ Then $$|M(x)|\le\frac{(0.013\log x-0.118)x}{\log^2x}.$$ In particular, taking $c_n=\mu(n)$ gives the exact analytic transfer from the weighted estimate to the summatory estimate needed for reciprocal Mobius decay. The starting-point correction is an explicit finite obligation.
-- source:
--   O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 8, https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Quantitative Abel-summation proof with an absolute starting-point correction and all real floor endpoints. Written by Codex.

import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
open Finset Nat Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

theorem summatory_explicit_log_decay_of_log_squared  (c : ℕ → ℝ) (a x : ℝ)
    (ha : 1 < a) (hax : a ≤ x)
    (hstart :
      |(∑ n ∈ Icc 1 ⌊a⌋₊, c n) -
        (∑ n ∈ Icc 1 ⌊a⌋₊, c n * Real.log (n : ℝ) ^ 2) / Real.log a ^ 2| ≤
          13 * a / (500 * Real.log a ^ 2))
    (hW : ∀ t ∈ Set.Icc a x,
      |∑ n ∈ Icc 1 ⌊t⌋₊, c n * Real.log (n : ℝ) ^ 2| ≤
        t * ((13 / 1000 : ℝ) * Real.log t - 18 / 125)) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, c n| ≤
      x * ((13 / 1000 : ℝ) * Real.log x - 59 / 500) / Real.log x ^ 2 := by sorry

end Helfgott
