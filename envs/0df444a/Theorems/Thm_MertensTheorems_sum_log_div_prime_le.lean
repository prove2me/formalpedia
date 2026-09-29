-- Prove2me | Theorems.Thm_MertensTheorems_sum_log_div_prime_le
-- name    : MertensTheorems.sum_log_div_prime_le
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T12:17:02.434054+00:00
-- url     : https://prove2.me/theorems/d09af852-f479-4509-a198-8f0ba56f9115
-- title:
--   Mertens' first theorem, with explicit constant
-- statement:
--   **Mertens' first theorem, in explicit upper-bound form.**
--
--   For every $N \ge 1$,
--
--   $$\sum_{p \le N} \frac{\log p}{p} \;\le\; \log N \;+\; \bigl(\log 4 + 4\bigr),$$
--
--   the sum running over primes $p \le N$.
--
--   The main term $\log N$ is sharp: Mertens proved that
--   $\sum_{p\le N}\tfrac{\log p}{p} = \log N + O(1)$, so the difference stays bounded, and this
--   statement pins the upper side with the **explicit** constant $\log 4 + 4$ rather than an
--   unspecified $O(1)$.
--
--   The estimate is the first of Mertens' three theorems and the elementary gateway to the others:
--   partial summation converts it into $\sum_{p \le N} \tfrac1p = \log\log N + O(1)$ and then into
--   $\prod_{p\le N}(1-\tfrac1p)^{-1} \asymp \log N$. It already encodes the correct density of the
--   primes in an averaged sense — enough for Chebyshev-type bounds — without requiring the prime
--   number theorem.
--
--   The proof is elementary: one bounds $\sum_{n \le N} \Lambda(n)/n$ using
--   $\log(N!) = \sum_{n\le N}\sum_{d \mid n}\Lambda(d)$ together with Stirling's estimate, and then
--   discards the contribution of the higher prime powers, which converges. The constant $\log 4$
--   enters through the standard bound on the central binomial coefficient.
--
--   **Formalization note.** The sum is over `(Finset.range (N+1)).filter Nat.Prime`, i.e. primes
--   $p \le N$, with $\log$ and the division taken in $\mathbb{R}$.
-- source:
--   F. Mertens, *Ein Beitrag zur analytischen Zahlentheorie* (1874); see Apostol, *Introduction to Analytic Number Theory*, Theorem 4.10, and Montgomery & Vaughan, *Multiplicative Number Theory I*, §2.2. Lean proof extracted from `Salt/Maynard/Mertens.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace MertensTheorems

theorem sum_log_div_prime_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p / p
      ≤ Real.log N + (Real.log 4 + 4) := by sorry

end MertensTheorems
