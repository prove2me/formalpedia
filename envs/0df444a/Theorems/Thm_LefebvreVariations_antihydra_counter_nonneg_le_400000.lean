-- Prove2me | Theorems.Thm_LefebvreVariations_antihydra_counter_nonneg_le_400000
-- name    : LefebvreVariations.antihydra_counter_nonneg_le_400000
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:37:35.548903+00:00
-- url     : https://prove2.me/theorems/d515d0eb-86a8-434b-8f20-6850d2537475
-- title:
--   Lefebvre's variations, No. 63 — on a theme by bbchallenge: the Antihydra counter stays nonnegative for 400000 steps
-- statement:
--   Let $a_0=8$, $a_{n+1}=\lfloor 3a_n/2\rfloor$, and let $b_0=0$,
--   $$
--   b_{n+1}=\begin{cases} b_n+2 & a_n \text{ even},\\ b_n-1 & a_n\text{ odd}.\end{cases}
--   $$
--   Then
--   $$
--   b_n\ge 0\qquad\text{for all } n\le 400000 .
--   $$
--   The minimum of $b_n$ over this range is $0$, attained only at $n=0$.
--
--   This is the Antihydra problem, the open question whether $b_n\ge 0$ for every $n$, at the range $n\le 400000$, extending the range $n\le 100000$ already proved on the platform.
--
--   **Formalization Note** The sequences are `a : ℕ → ℕ` and `b : ℕ → ℤ` with the stated initial values and recurrences as hypotheses; natural-number division is floor division. The conclusion is `∀ n, n ≤ 400000 → b n ≥ 0`.
--
--   **Why this is a variation.** This is a variation on the open platform problem Antihydra.cumulative_odd_never_more_than_twice_even (b_n >= 0 for all n). It extends the verified range from n <= 100000, already proved on the platform as Antihydra.nonneg_first_100000, to n <= 400000. The statement for all n remains open.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   The Antihydra Turing machine of the bbchallenge.org community (a Busy Beaver, 6 states, cryptid). The statement of the recurrences is that of the platform problem Antihydra.cumulative_odd_never_more_than_twice_even, whose recorded source is google-deepmind/formal-conjectures, FormalConjectures/Other/BeaverMathOlympiad.lean (Antihydra); the link between the machine and this counter was not checked against the bbchallenge write-up (cited from memory). The range n <= 400000 was checked by direct computation of the sequence with exact integers; the platform already has n <= 100000 (Antihydra.nonneg_first_100000).

import Mathlib

namespace LefebvreVariations

/-- The Antihydra problem (BB(6) cryptid) at a larger verified range: starting from `a₀ = 8`
with `a_{n+1} = ⌊3 a_n / 2⌋`, the counter `b` (plus `2` on an even `a_n`, minus `1` on an odd
one) stays nonnegative for the first `400000` steps. A direct computation of the sequence
confirms it (minimum `0`, attained only at `n = 0`).
Source: the Antihydra machine of the bbchallenge.org community (Busy Beaver, 6 states);
the reduction to this pair of recurrences is the platform's own statement of the problem
(cited from memory). -/
theorem antihydra_counter_nonneg_le_400000
    (a : Nat → Nat) (b : Nat → Int)
    (a_ini : a 0 = 8)
    (a_rec : ∀ n, a (n + 1) = (3 * a n) / 2)
    (b_ini : b 0 = 0)
    (b_rec : ∀ n, b (n + 1) = if a n % 2 = 0 then b n + 2 else b n - 1) :
    ∀ n, n ≤ 400000 → b n ≥ 0 := by
  sorry

end LefebvreVariations
