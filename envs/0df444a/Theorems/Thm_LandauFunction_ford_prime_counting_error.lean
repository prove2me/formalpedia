-- Prove2me | Theorems.Thm_LandauFunction_ford_prime_counting_error
-- name    : LandauFunction.ford_prime_counting_error
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:30:59.822601+00:00
-- url     : https://prove2.me/theorems/83cea929-bd50-4781-abec-1bee638b5093
-- title:
--   Prime number theorem with Ford's error term
-- statement:
--   There is a constant $c>0$ such that, as $x\to\infty$,
--
--   $$\pi(x)-\mathrm{Li}(x)=O\!\left(x\exp\!\left(-c(\ln x)^{3/5}(\ln\ln x)^{-1/5}\right)\right),$$
--
--   where $\pi(x)$ is the number of primes $p\le x$ and $\mathrm{Li}(x)=\int_2^x dt/\ln t$.
--
--   This is the error term in the prime number theorem that the source feeds into the asymptotic formula for $\ln g(n)$ in terms of $\mathrm{Li}^{-1}$.
--
--   **Formalization Note** $\pi(x)$ for real $x$ is `Nat.primeCounting ⌊x⌋₊`; the real powers are `Real.rpow`.
-- source:
--   K. Ford, Proc. London Math. Soc. 85 (2002) 565–633; as quoted in Wikipedia, "Landau's function", revision oldid=1303222269 (https://en.wikipedia.org/w/index.php?title=Landau%27s_function&oldid=1303222269), paragraph "If π(x) − Li(x) = O(R(x)) … we may take R(x) = x exp(−c (ln x)^{3/5} (ln ln x)^{−1/5}) for some constant c > 0 by Ford", ref. [4].

import Mathlib
import Definitions.Def_LandauFunction_logIntegral

namespace LandauFunction
theorem ford_prime_counting_error :
    ∃ c : ℝ, 0 < c ∧
      (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) - logIntegral x) =O[Filter.atTop]
        (fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((3 : ℝ) / 5) *
          Real.log (Real.log x) ^ (-(1 : ℝ) / 5))) := by sorry
end LandauFunction
