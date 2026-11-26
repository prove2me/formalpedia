-- Prove2me | Theorems.Thm_LefebvreVariations_markov_unicity_le_300
-- name    : LefebvreVariations.markov_unicity_le_300
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-25T23:48:04.165274+00:00
-- url     : https://prove2.me/theorems/42145e50-5b64-5a4b-9333-229fa3527580
-- title:
--   Lefebvre's variations, No. 59 — on a theme by Frobenius: the Markov unicity conjecture for m ≤ 300
-- statement:
--   For every integer $m$ with $1\le m\le 300$: if $x^2+y^2+m^2=3xym$ has a solution in natural numbers $x,y$, then there is exactly one pair $(p_1,p_2)$ with
--   $$
--   0<p_1\le p_2\le m,\qquad p_1^2+p_2^2+m^2=3\,p_1p_2\,m .
--   $$
--   The integers $m\le 300$ that occur in a solution are the Markov numbers $1,2,5,13,29,34,89,169,194,233$.
--
--   This is the Markov (Frobenius) unicity conjecture in the range $m\le 300$: each Markov number is the largest entry of a single Markov triple.
--
--   **Formalization Note** The hypothesis is the same as in the unrestricted problem: some pair of naturals $x,y$, not required to be at most $m$, solves $x^2+y^2+m^2=3xym$. The conclusion is unique existence of a pair $0<p_1\le p_2\le m$. The only added hypothesis is `m ≤ 300`.
--
--   **Why this is a variation.** This is a variation on the open platform problem markov_unicity_conjecture, the Markov (Frobenius) unicity conjecture for all m. It adds the hypothesis m <= 300 and keeps the parent's statement otherwise unchanged. The conjecture for unbounded m remains open.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   A. Markoff, Sur les formes quadratiques binaires indefinies, Math. Ann. 15 (1879), 381-406 (the equation; cited from memory). The unicity conjecture is attributed to G. Frobenius, Sitzungsber. Preuss. Akad. Wiss. (1913) (cited from memory). The values 1, 2, 5, 13, 29, 34, 89, 169, 194, 233 and the absence of a second triple for m <= 300 were checked by direct enumeration for this variation.

import Mathlib

namespace LefebvreVariations

/-- The Markov unicity conjecture (Frobenius 1913) at its first non-trivial range: for every
`m ≤ 300` that occurs in a solution of `x² + y² + z² = 3xyz`, there is exactly one pair
`x ≤ y ≤ m` completing it to a solution with largest entry `m`. The Markov numbers up to
300 are `1, 2, 5, 13, 29, 34, 89, 169, 194, 233`.
Source: G. Frobenius, Sitzungsber. Preuss. Akad. Wiss. (1913), who stated the conjecture;
A. Markoff, Math. Ann. 15 (1879) for the equation. Unicity is known for prime-power and
twice-prime-power `m` (Baragar, Button, Schmutz; cited from memory, not checked).

**Formalization Note** The hypothesis is the parent's: some pair of naturals `x, y` solves
`x² + y² + m² = 3xym` (not required to be below `m`). The conclusion is unique existence of
`(p₁, p₂)` with `0 < p₁ ≤ p₂ ≤ m` solving the same equation. The only added hypothesis is
`m ≤ 300`. -/
theorem markov_unicity_le_300 : ∀ m : ℕ, 1 ≤ m → m ≤ 300 →
    (∃ x y : ℕ, x ^ 2 + y ^ 2 + m ^ 2 = 3 * x * y * m) →
    ∃! p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ p.1 ≤ p.2 ∧ p.2 ≤ m ∧
      p.1 ^ 2 + p.2 ^ 2 + m ^ 2 = 3 * p.1 * p.2 * m := by
  sorry

end LefebvreVariations
