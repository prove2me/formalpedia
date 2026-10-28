-- Prove2me | Theorems.Thm_OAI_OddGoldbach23_finite_sieve_certificate
-- name    : OAI.OddGoldbach23.finite_sieve_certificate
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-25T07:21:55.96826+00:00
-- url     : https://prove2.me/theorems/13091c6f-2fef-4cbe-b70a-0a3e74bf6cfd
-- title:
--   A certified 1000-prime finite sieve weight bound
-- statement:
--   There exists a set $Q$ of exactly $1000$ odd primes, all at most $7927$, such that
--
--   $$
--   \sum_{\substack{a,b\in Q\\b<a}}
--   \prod_{\substack{p\mid a-b\\p>2\text{ prime}}}\frac{p-1}{p-2}
--   \le 867861.
--   $$
--
--   The product runs over distinct odd prime divisors of the positive difference $a-b$. The outer sum counts each unordered pair of distinct elements of $Q$ once.
--
--   This finite bound controls the off-diagonal term in a second-moment estimate for sums of two odd primes. It is a reusable input toward refining the existing $25$-prime Odd Goldbach formalization; this statement alone does not assert a new Goldbach bound.
-- source:
--   Finite certificate constructed on 2026-10-25 as a refinement of the existing 25-prime Schnirelmann–Mann formalization, https://prove2.me/theorems/ba75c64f-9452-4582-83b3-77b31da8e4dc . Mathematical method: Riesel–Vaughan (1983), On sums of primes, section 6. The 1000-prime parameter and exact computational bound are this contribution, not a quoted theorem of that paper.

import Mathlib
open Finset

theorem OAI.OddGoldbach23.finite_sieve_certificate :
    ∃ Q : Finset ℕ, Q.card = 1000 ∧
    (∀ p ∈ Q, p.Prime ∧ p ≠ 2 ∧ p ≤ 7927) ∧
    (∑ a ∈ Q, ∑ b ∈ Q, if b < a then
      (∏ p ∈ (a-b).primeFactors, if 2 < p then ((p : ℝ)-1)/((p : ℝ)-2) else 1)
      else 0) ≤ (867861 : ℝ) := by sorry
