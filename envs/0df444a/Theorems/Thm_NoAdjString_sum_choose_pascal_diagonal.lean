-- Prove2me | Theorems.Thm_NoAdjString_sum_choose_pascal_diagonal
-- name    : NoAdjString.sum_choose_pascal_diagonal
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-25T17:12:40.221985+00:00
-- url     : https://prove2.me/theorems/a69c3bfe-bac5-4216-ac08-6867c39c5bb0
-- title:
--   Pascal-diagonal sum equals fib(n+2)
-- statement:
--   The sum along a diagonal of Pascal's triangle equals a Fibonacci number:
--
--   $$\sum_{k=0}^{n} \binom{n+1-k}{k} = \mathrm{fib}(n+2).$$
--
--   The sum is identified with the count of length-$n$ binary strings with no adjacent ones, grouped by the number of ones, and that count is $\mathrm{fib}(n+2)$.
-- source:
--   Kenneth H. Rosen, Discrete Mathematics and Its Applications, 8th ed., McGraw-Hill 2019. The no-consecutive-ones count is the worked example on bit strings without consecutive 1s in Section 8.1 (Applications of Recurrence Relations); the exact-k binomial count is the restricted-combinations (gap) argument of Chapter 6.

import Definitions.Def_NoAdjacentBinaryStrings
import Mathlib.Data.Nat.Fib.Basic

open Finset Function

namespace NoAdjString

theorem sum_choose_pascal_diagonal (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Nat.choose (n + 1 - k) k = Nat.fib (n + 2) := by sorry

end NoAdjString
