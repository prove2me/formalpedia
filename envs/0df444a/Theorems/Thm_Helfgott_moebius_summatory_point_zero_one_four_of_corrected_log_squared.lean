-- Prove2me | Theorems.Thm_Helfgott_moebius_summatory_point_zero_one_four_of_corrected_log_squared
-- name    : Helfgott.moebius_summatory_point_zero_one_four_of_corrected_log_squared
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T00:27:02.499743+00:00
-- url     : https://prove2.me/theorems/e1ef0032-d8a8-4452-84ee-a169134f67ff
-- title:
--   Convert the corrected log-squared Mobius bound to a high-range Mertens bound
-- statement:
--   Suppose $|M(10^{26})|\le10^{26}/4345$ and $|\sum_{n\le N}\mu(n)\log^2n|\le N(0.014\log N-0.23)$ for every natural $N\ge10^{26}$. Then every real $x\ge10^{27}$ satisfies $|M(x)|\le0.014x/\log x$, where $M(x)=\sum_{n\le\lfloor x\rfloor}\mu(n)$. Both the anchor bound and the weighted estimate remain explicit hypotheses.
-- source:
--   Independent standard-kernel corrected Mobius conversion, related to O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Written by Codex.

import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

theorem moebius_summatory_point_zero_one_four_of_corrected_log_squared 
    (x : ℝ) (hx : 1000000000000000000000000000 ≤ x)
    (hanchor : |∑ n ∈ Icc 1 100000000000000000000000000,
      ((moebius n : ℤ) : ℝ)| ≤ (100000000000000000000000000 : ℝ) / 4345)
    (hW : ∀ N : ℕ, 100000000000000000000000000 ≤ N →
      |∑ n ∈ Icc 1 N, ((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ 2| ≤
        (N : ℝ) * ((7 / 500) * Real.log (N : ℝ) - 23 / 100)) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, ((moebius n : ℤ) : ℝ)| ≤
      (7 / 500) * x / Real.log x := by sorry

end Helfgott
