-- Prove2me | Theorems.Thm_GoldbachSieve_survivor_of_prime
-- name    : GoldbachSieve.survivor_of_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T17:39:13.189211+00:00
-- url     : https://prove2.me/theorems/a0a806ed-4d9a-43d7-86a5-835434486595
-- title:
--   A prime inside the interval is a sieve survivor
-- statement:
--   If $q$ is prime and $\max(2, lo) \le q \le hi$, then $q$ survives sieving by all primes up to $c$:
--
--   $$q \in S(lo, hi, c).$$
--
--   The reason is that survivorship only forbids *proper* prime divisors up to $c$, and a prime has none: if a prime $r \le c$ divides $q$ then $r = q$. Consequently every prime in the interval belongs to the survivor set, whichever cutoff is used.
--
--   **Why it matters.** A computation that exhibits a prime decomposition $n = p + q$ with $q$ prime therefore produces a witness for the survivor-based coverage statements without any further work; this is the step that turns a primality proof into a sieve membership.
--
--   **Formalization Note.** Immediate from `GoldbachSieve.mem_survivors` and `Nat.prime_dvd_prime_iff_eq`.
-- source:
--   GoldbachSieve.survivors (platform definition); Richstein 2001 segmented sieve.

import Definitions.Def_GoldbachSieve

namespace GoldbachSieve

theorem survivor_of_prime {lo hi c q : ℕ} (hq : q.Prime)
    (h1 : max 2 lo ≤ q) (h2 : q ≤ hi) : q ∈ survivors lo hi c := by sorry

end GoldbachSieve
