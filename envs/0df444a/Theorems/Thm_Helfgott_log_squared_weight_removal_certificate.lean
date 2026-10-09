-- Prove2me | Theorems.Thm_Helfgott_log_squared_weight_removal_certificate
-- name    : Helfgott.log_squared_weight_removal_certificate
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T19:37:16.596708+00:00
-- url     : https://prove2.me/theorems/c2a7b936-3d3f-448c-a2dd-3ea0fb6ebb67
-- title:
--   Complete removal of the squared logarithmic summation weight
-- statement:
--   Let $c_n$ be any real sequence, $M(t)=\sum_{1\le n\le\lfloor t\rfloor}c_n$, and $W(t)=\sum_{1\le n\le\lfloor t\rfloor}c_n(\log n)^2$. For real endpoints $1<a\le x$, the function $W(t)/(t(\log t)^3)$ is integrable on $[a,x]$ and
--   $$M(x)=M(a)-\frac{W(a)}{(\log a)^2}+\frac{W(x)}{(\log x)^2}+2\int_a^x\frac{W(t)}{t(\log t)^3}\,dt.$$
--   Consequently,
--   $$|M(x)|\le\left|M(a)-\frac{W(a)}{(\log a)^2}\right|+\frac{|W(x)|}{(\log x)^2}+2\int_a^x\frac{|W(t)|}{t(\log t)^3}\,dt.$$
--   This transfers estimates for logarithmically weighted sums, including the weighted Mobius sum, to ordinary summatory estimates while retaining the exact initial correction.
-- source:
--   Abel summation applied to the inverse squared logarithm; relates to O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), Lemma 8.1, https://www.impan.pl/shop/en/publication/transaction/download/product/82991. The integral in the exact identity has the positive sign, independently checked by its derivative. Written by Codex.

import Mathlib
open Finset Nat Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

theorem log_squared_weight_removal_certificate  (c : ℕ → ℝ) (a x : ℝ)
    (ha : 1 < a) (hax : a ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2) /
        (t * Real.log t ^ 3)) volume a x ∧
    (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d) =
      (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d) -
        (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log a ^ 2 +
        (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log x ^ 2 +
        2 * ∫ t in a..x,
          (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2) /
            (t * Real.log t ^ 3) ∧
    |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d| ≤
      |(∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d) -
        (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log a ^ 2| +
        |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d * Real.log (d : ℝ) ^ 2| / Real.log x ^ 2 +
        2 * ∫ t in a..x,
          |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2| /
            (t * Real.log t ^ 3) := by sorry

end Helfgott
