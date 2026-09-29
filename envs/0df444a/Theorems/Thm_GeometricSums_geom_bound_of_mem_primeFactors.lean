-- Prove2me | Theorems.Thm_GeometricSums_geom_bound_of_mem_primeFactors
-- name    : GeometricSums.geom_bound_of_mem_primeFactors
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:12:02.924741+00:00
-- url     : https://prove2.me/theorems/84a216df-06d2-42ed-88a0-c7a1768b128d
-- title:
--   A geometric sum bound at an odd prime factor
-- statement:
--   **A uniform bound for a truncated geometric series at an odd prime.**
--
--   Let $\ell$ be odd and $p$ a prime factor of $\ell$; then $p$ is odd, hence $p \ge 3$ and the
--   ratio $r = 2/p$ satisfies $r \le 2/3 < 1$. For every truncation length $K$,
--
--   $$\sum_{j=1}^{K} \left(\frac{2}{p}\right)^{j} \;\le\; \frac{2}{p-2}.$$
--
--   The right-hand side is the value of the full infinite series,
--   $\sum_{j\ge1} r^{j} = \tfrac{r}{1-r} = \tfrac{2/p}{1 - 2/p} = \tfrac{2}{p-2}$, so the statement
--   is that every partial sum is bounded by the limit — true because all terms are positive.
--
--   The role of the oddness hypothesis is precisely to keep $p \ne 2$: at $p = 2$ the ratio is $1$,
--   the series diverges, and the right-hand side $2/(p-2)$ is undefined. Requiring $p \mid \ell$
--   with $\ell$ odd is a convenient way to carry that constraint through a larger argument.
--
--   Bounds of this shape arise in sieve and expansion arguments where one sums a geometric
--   progression in $2/p$ over the prime factors of a modulus and needs a bound uniform in the
--   truncation.
--
--   **Formalization note.** `\u2113.primeFactors` is the finset of primes dividing $\ell$; the sum runs
--   over $1 \le j \le K$, so the empty case $K = 0$ is included and the bound is then trivial.
-- source:
--   Elementary. Lean proof extracted from `Salt/Brun/M3Expansion.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace GeometricSums

theorem geom_bound_of_mem_primeFactors {ℓ p : ℕ} (hℓodd : Odd ℓ) (hp : p ∈ ℓ.primeFactors)
    (K : ℕ) :
    ∑ j ∈ Finset.Icc 1 K, ((2 : ℝ) / (p : ℝ)) ^ j ≤ (2 : ℝ) / ((p : ℝ) - 2) := by sorry

end GeometricSums
