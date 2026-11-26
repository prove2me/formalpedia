-- Prove2me | Theorems.Thm_LehmerTotient_lehmer_prime_power
-- name    : LehmerTotient.lehmer_prime_power
-- status  : Open
-- author  : @fangshuming
-- created : 2026-11-26T09:22:40.36134+00:00
-- url     : https://prove2.me/theorems/87438792-5f92-4d67-b386-b85d627d363c
-- title:
--   Prime powers with $\varphi(n)\mid n-1$ are prime
-- statement:
--   Let $n>1$ be a prime power, and suppose that $\varphi(n)$ divides $n-1$. Then $n$ is prime. This is a known elementary special case of Lehmer's totient problem, excluding the square-free products of several primes that a composite solution would have to be.
-- source:
--   D. H. Lehmer, On Euler's totient function, Bull. Amer. Math. Soc. 38 (1932), 745–751, Theorem 1 and Case I (t=1), https://doi.org/10.1090/S0002-9904-1932-05521-5

import Mathlib

namespace LehmerTotient
theorem lehmer_prime_power {n : Nat} (hn : 1 < n) (hp : IsPrimePow n)
    (h : Nat.totient n ∣ n - 1) : Nat.Prime n := by sorry
end LehmerTotient
