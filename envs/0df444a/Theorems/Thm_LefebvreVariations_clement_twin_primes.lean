-- Prove2me | Theorems.Thm_LefebvreVariations_clement_twin_primes
-- name    : LefebvreVariations.clement_twin_primes
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T23:28:24.731841+00:00
-- url     : https://prove2.me/theorems/a6483ef6-24dd-4abe-bd30-252aba9f6c28
-- title:
--   Lefebvre's variations: Clement's Wilson-type criterion for twin primes
-- statement:
--   This is Clement's Wilson-type criterion for twin primes.
--
--   For every integer $n\ge2$,
--
--   $$
--   n\ \text{and}\ n+2\ \text{are both prime}\iff n(n+2)\ \Big|\ 4\big((n-1)!+1\big)+n .
--   $$
--
--   It is the analogue for twin primes of Wilson's theorem, which characterises a single prime $p$ by $p\mid(p-1)!+1$. The twin prime conjecture asserts that there are infinitely many $n$ with both $n$ and $n+2$ prime; this criterion turns the conjecture into a statement about divisibility of factorials.
--
--   **Formalization Note** The case $n=1$ is excluded: $3\mid 4\cdot2+1=9$ holds although $1$ is not prime.
-- source:
--   P. A. Clement, Congruences for sets of primes, Amer. Math. Monthly 56 (1949), 23–25 (cited from memory; the criterion for twin primes). Wilson's theorem: Hardy and Wright, An Introduction to the Theory of Numbers, 6th ed., Oxford Univ. Press, 2008, Theorem 80. Parent problem: twin_prime_conjecture.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- Clement's criterion for twin primes (a Wilson-type characterisation): for `n ≥ 2`,
`n` and `n + 2` are both prime iff `n (n + 2) ∣ 4 ((n - 1)! + 1) + n`.
(`n = 1` is the one exception: `3 ∣ 9`.)
P. A. Clement, "Congruences for sets of primes", Amer. Math. Monthly 56 (1949), 23–25. -/
theorem clement_twin_primes (n : ℕ) (hn : 2 ≤ n) :
    (n.Prime ∧ (n + 2).Prime) ↔ n * (n + 2) ∣ 4 * ((n - 1).factorial + 1) + n := by
  sorry

end LefebvreVariations
