-- Prove2me | Theorems.Thm_NoAdjString_card_noAdjacentStrings
-- name    : NoAdjString.card_noAdjacentStrings
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-25T17:12:44.02898+00:00
-- url     : https://prove2.me/theorems/66057474-5dda-471a-90b0-9d5c665b0571
-- title:
--   Total count of no-adjacent strings is fib(n+2)
-- statement:
--   The total number of length-$n$ binary strings with no adjacent ones is the Fibonacci number
--
--   $$\#(\mathrm{noAdjacentStrings}\, n) = \mathrm{fib}(n+2).$$
--
--   A valid string of length $n+2$ either ends in $0$, leaving an arbitrary valid prefix of length $n+1$, or ends in $01$, leaving an arbitrary valid prefix of length $n$. The bijection $\mathrm{noAdjacentStringsRecurrenceEquiv}$ realizes exactly this recurrence, with base cases one string of length $0$ and two strings of length $1$.
-- source:
--   Kenneth H. Rosen, Discrete Mathematics and Its Applications, 8th ed., McGraw-Hill 2019. The no-consecutive-ones count is the worked example on bit strings without consecutive 1s in Section 8.1 (Applications of Recurrence Relations); the exact-k binomial count is the restricted-combinations (gap) argument of Chapter 6.

import Definitions.Def_NoAdjacentGapEquiv
import Mathlib.Data.Nat.Fib.Basic

open Finset Function

namespace NoAdjString

theorem card_noAdjacentStrings (n : ℕ) :
    (noAdjacentStrings n).card = Nat.fib (n + 2) := by sorry

end NoAdjString
