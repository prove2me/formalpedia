-- Prove2me | Theorems.Thm_LefebvreVariations_markov_unicity_prime_power
-- name    : LefebvreVariations.markov_unicity_prime_power
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:37:19.020637+00:00
-- url     : https://prove2.me/theorems/c49a7f45-fbfb-40d7-bba2-55982e362465
-- title:
--   Lefebvre's variations, No. 61 — on a theme by Frobenius: the Markov unicity conjecture for prime powers
-- statement:
--   Let $m$ be a prime power. If $x^2+y^2+m^2=3xym$ has a solution in natural numbers $x,y$, then there is exactly one pair $(p_1,p_2)$ with
--   $$
--   0<p_1\le p_2\le m,\qquad p_1^2+p_2^2+m^2=3\,p_1p_2\,m .
--   $$
--
--   This is the Markov (Frobenius) unicity conjecture when the largest entry of the triple is a prime power, a case proved in the literature.
--
--   **Formalization Note** `IsPrimePow m` is Mathlib's predicate for $m=p^k$ with $p$ prime and $k\ge 1$, so $m=1$ is excluded. The hypothesis is the parent's: some pair of naturals $x,y$, not required to be at most $m$, solves $x^2+y^2+m^2=3xym$.
--
--   **Why this is a variation.** This is a variation on the open platform problem markov_unicity_conjecture. It adds the hypothesis that m is a prime power, a case reported as proved in the literature (Schmutz, Button, with a later elementary proof by Zhang). The conjecture for all m remains open.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Verified by web search (abstracts and bibliographic records, full texts not read): A. Baragar, On the unicity conjecture for Markoff numbers, Canad. Math. Bull. 39 (1996), no. 1, 3-9, which proves unicity when m, 3m-2 or 3m+2 is a prime, twice a prime or four times a prime (so primes, not general prime powers). P. Schmutz, Systoles of arithmetic surfaces and the Markoff spectrum, Math. Ann. 305 (1996), 191-204, treats the uniqueness question by hyperbolic geometry; the prime-power result is attributed to Button and Schmutz in secondary sources (a lecture note), not checked in the papers themselves. Y. Zhang, An elementary proof of uniqueness of Markoff numbers which are prime powers, arXiv:math/0606283 (title and arXiv number verified; journal not checked). Cited from memory, not verified: M. Button's papers on the prime case (c. 1998) and on the general case (J. Number Theory, c. 2001); G. Frobenius, Sitzungsber. Preuss. Akad. Wiss. (1913), who posed the conjecture. The parent on the platform, markov_unicity_conjecture, itself notes the prime-power case as proved.

import Mathlib

namespace LefebvreVariations

/-- The Markov unicity conjecture (Frobenius 1913) when the largest entry `m` of the triple is
a prime power: if `m` occurs in a solution of `x² + y² + z² = 3xyz`, exactly one pair
`x ≤ y ≤ m` completes it to a solution with largest entry `m`.
Source: A. Baragar, On the unicity conjecture for Markoff numbers, Canad. Math. Bull. 39
(1996) (primes); P. Schmutz and M. Button extended it to prime powers and twice prime powers
(all three cited from memory, not checked against the papers). -/
theorem markov_unicity_prime_power : ∀ m : ℕ, IsPrimePow m →
    (∃ x y : ℕ, x ^ 2 + y ^ 2 + m ^ 2 = 3 * x * y * m) →
    ∃! p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ p.1 ≤ p.2 ∧ p.2 ≤ m ∧
      p.1 ^ 2 + p.2 ^ 2 + m ^ 2 = 3 * p.1 * p.2 * m := by
  sorry

end LefebvreVariations
