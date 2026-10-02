-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_sum_divisors_sq_eq_prod
-- name    : OddPerfectNumber.Kernel.sum_divisors_sq_eq_prod
-- status  : Open
-- author  : @WillR
-- created : 2026-10-02T02:32:44.033432+00:00
-- url     : https://prove2.me/theorems/d3e5b799-a846-4e2a-9c5a-fa7e02a66c54
-- title:
--   The divisor sum of $m^2$ factors over the primes of $m$
-- statement:
--   For $m \neq 0$,
--
--   $$\sigma(m^2) \;=\; \prod_{t \in m.\mathrm{primeFactors}} \; \sum_{k < 2\,v_t(m)+1} t^k.$$
--
--   This is Mathlib's `Nat.sum_divisors` applied at $n := m^2$, together with $(m^2).\mathrm{primeFactors} = m.\mathrm{primeFactors}$ and $(m^2).\mathrm{factorization}\ t = 2\,m.\mathrm{factorization}\ t$.
--
--   **Why this is the key step for the second Dris equation.** In the $k=5$ residual $h_2$ reads $\sigma(m^2) = p^5 d_1^2 q r$. The identity above rewrites the left-hand side as a product of the local factors $\sigma(t^{2v_t(m)})$ over the primes dividing $m$. From that product one obtains (a) existence of an incoming $p$-source whenever $p \mid \sigma(m^2)$, and (b) the exact valuation budget
--
--   $$\sum_{t \mid m} v_p\!\left(\sigma\left(t^{2v_t(m)}\right)\right) = 5,$$
--
--   because $p \nmid s$ in the two-prime case, so the whole $p$-adic content of $h_2$ sits in the factor $p^5$. Both are immediate corollaries of the product decomposition and neither is available without it.

import Mathlib

namespace OddPerfectNumber.Kernel

/-- The divisor sum of `m^2` splits as a product over the primes of `m`. -/
theorem sum_divisors_sq_eq_prod (m : Nat) (hm : m != 0) :
    (∑ d ∈ (m ^ 2).divisors, d) = ∏ t ∈ m.primeFactors, ∑ k ∈ Finset.range (m.factorization t * 2 + 1), t ^ k := by
  sorry

end OddPerfectNumber.Kernel
