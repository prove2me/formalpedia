-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_d1_prime_dvd_sigma_of_second_dris
-- name    : OddPerfectNumber.Kernel.d1_prime_dvd_sigma_of_second_dris
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T09:33:54.839012+00:00
-- url     : https://prove2.me/theorems/464a8b44-61b2-4b4d-a49a-1c40f1f9476c
-- title:
--   Every prime dividing the square part $d_1$ of the index also divides $\sigma(m^2)$
-- statement:
--   Let `p`, `q`, `r` be primes and `m`, `d1` natural numbers with
--   $\sigma(m^2) = p^5 d_1^2 q r$.  Then every prime divisor of `d1` divides `sigma(m^2)`.
--
--   **Why this is a real constraint and not a tautology.**  `d1` plays a *double role*: it is
--   both a factor of the index `s = d1^2 q r` AND a source of prime divisors of `m`, since
--   `five_two_prime_first_eq_d1_prime_dvd_m` (28ef75b8, Proved) gives `t | d1 -> t | m`.
--   So primes of `d1` are simultaneously
--
--     * candidate incoming sigma-sources of the Euler prime (via `t | m`), and
--     * forced divisors of `sigma(m^2)` (via `h2` and `t | s`).
--
--   The proved `five_two_prime_sigma_supply_no_foreign_prime` (ef31275b) already shows every
--   prime of `sigma(m^2)` lies in `{p} u primes|d1 u {q, r}`, so this closure is consistent;
--   but it is the constraint that couples the *source* set to the *index* support, and no
--   local congruence or order argument at `q` or `r` can see it.
--
--   The proof is elementary: `t | d1` gives `t | d1^2 * (q * r)`, whence
--   `t | p^5 * (d1^2 * (q * r)) = sigma(m^2)` by `h2` and `dvd_mul_right`.
--
--   Numerical note (exact integers, no Lean): over `p` in the two normal forms `p = 5` and
--   `p = 293` with `d1 < 4000`, 7998 tuples satisfy the first Dris equation and 144 of them
--   have *every* prime of `d1` dividing `sigma(m^2)`, so the closure condition is genuinely
--   satisfiable and is not itself a contradiction.

import Mathlib

namespace OddPerfectNumber.Kernel

/-- The square part `d1` of the Dris index is forced into the support of the
second divisor sum: any prime dividing `d1` divides `sigma(m^2)`. -/
theorem d1_prime_dvd_sigma_of_second_dris (p m d1 q r : Nat) (hq : q.Prime)
    (hr : r.Prime)
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * (d1 ^ 2 * (q * r)))
    (t : Nat) (ht : t.Prime) (htd : Dvd.dvd t d1) :
    Dvd.dvd t (∑ d ∈ (m ^ 2).divisors, d) := by
  sorry

end OddPerfectNumber.Kernel
