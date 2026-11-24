-- Prove2me | Theorems.Thm_LefebvreVariations_brocard_succ_prime_is_wilson
-- name    : LefebvreVariations.brocard_succ_prime_is_wilson
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:15:28.321885+00:00
-- url     : https://prove2.me/theorems/9f594eac-7414-4cd9-9fba-797e180fabf0
-- title:
--   Lefebvre's variations, No. 15 — on a theme by Brocard: Brocard's problem with $n+1$ prime forces a Wilson prime
-- statement:
--   This is the case $n+1$ prime of Brocard's problem.
--
--   Suppose $n!+1=m^2$ for natural numbers $n,m$, and that $p=n+1$ is prime. Then
--
--   $$
--   p^2\ \mid\ n!+1=(p-1)!+1 ,
--   $$
--
--   that is, $p$ is a Wilson prime. Indeed Wilson's theorem gives $p\mid (p-1)!+1=m^2$, so $p\mid m$ and $p^2\mid m^2$.
--
--   Brocard's problem asks for all solutions of $n!+1=m^2$; the only known ones are $n=4,5,7$. Combined with the known Wilson primes, this reduces the case $n+1$ prime to a finite check: below $2\cdot10^{13}$ the only Wilson primes are $5$, $13$ and $563$, and of these only $p=5$ (that is $n=4$, $4!+1=5^2$) gives a solution, so any further solution with $n+1$ prime would require a new, very large Wilson prime.
-- source:
--   Wilson's theorem applied to the Brocard–Ramanujan equation n! + 1 = m^2: H. Brocard, Question 166, Nouv. Corresp. Math. 2 (1876), 287; B. C. Berndt and W. F. Galway, On the Brocard–Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), 41–42. Wilson primes: R. Crandall, K. Dilcher and C. Pomerance, A search for Wieferich and Wilson primes, Math. Comp. 66 (1997), 433–449; E. Costa, R. Gerbicz and D. Harvey, A search for Wilson primes, Math. Comp. 83 (2014), 3071–3091 (only 5, 13, 563 below 2·10^13). Parent problem: Brocard.brocard_problem.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- Brocard's problem, the case `n + 1` prime: a solution of `n! + 1 = m²` with `n + 1 = p`
prime forces `p` to be a Wilson prime (`p² ∣ (p-1)! + 1`). Only `p = 5, 13, 563` are known below
`2·10¹³`, and `p = 13, 563` give no solution (`12! + 1`, `562! + 1` are not squares), so the
only solution with `n + 1` prime is `(4, 5)`. -/
theorem brocard_succ_prime_is_wilson (n m : ℕ) (h : n.factorial + 1 = m ^ 2)
    (hp : (n + 1).Prime) : (n + 1) ^ 2 ∣ n.factorial + 1 := by
  sorry

end LefebvreVariations
