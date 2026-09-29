-- Prove2me | Theorems.Thm_OddPerfectNumber_sigma_prime_pow_ne_two_mul_sq_of_six_dvd
-- name    : OddPerfectNumber.sigma_prime_pow_ne_two_mul_sq_of_six_dvd
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-08T20:50:18.63396+00:00
-- url     : https://prove2.me/theorems/cfd89a00-9326-4ee9-8fc2-eae61dea8d7b
-- title:
--   $\sigma(p^k) \ne 2m^2$ when $6 \mid k+1$
-- statement:
--   Write $\sigma(n)=\sum_{d\mid n} d$ for the sum-of-divisors function.
--
--   Let $p$ be an odd prime and let $k$ be a natural number with $6 \mid k+1$. Then the equation
--
--   $$\sigma(p^{k}) \;=\; 2m^{2}$$
--
--   has no solution in natural numbers $m$.
--
--   Equivalently, $\tfrac{1}{2}\sigma(p^{k}) = \tfrac{1}{2}\bigl(1+p+\cdots+p^{k}\bigr)$ is never a perfect square when $6 \mid k+1$.
--
--   **Why this is relevant to odd perfect numbers.** If $N = p^{k}m^{2}$ is an odd perfect number in Euler form ($p$ prime, $p \equiv k \equiv 1 \pmod 4$, $p \nmid m$), then multiplicativity of $\sigma$ gives the Euler equation $\sigma(p^{k})\sigma(m^{2}) = 2p^{k}m^{2}$. Since $p \nmid \sigma(p^{k})$ and $k$ is odd, one gets $\tfrac{1}{2}\sigma(p^{k}) \mid m^{2}$, and writing $2m^{2} = \sigma(p^{k})\,s$, $\sigma(m^{2}) = p^{k} s$ shows that $m^{2} \le p^{k}$ forces $s = 1$, i.e. $2m^{2} = \sigma(p^{k})$. The statement above therefore rules out $m^{2} \le p^{k}$ whenever $6 \mid k+1$; for the special exponents $k \equiv 1 \pmod 4$ with $k \ge 5$ this covers $k \equiv 5 \pmod{12}$, in particular the first case $k = 5$.
--
--   **Proof idea.** Writing $k+1 = 6w$ and $y = p^{w}$, the geometric series identity factors $\sigma(p^{k}) = \sigma(p^{2w-1})\,(y^{4}+y^{2}+1)$, where $\sigma(p^{2w-1})$ is even and divides $y^{2}-1$. Hence $2m^{2} = \sigma(p^k)$ becomes
--
--   $$\tfrac{1}{2}\sigma(p^{2w-1}) \cdot (y^{2}+y+1)(y^{2}-y+1) = m^{2}.$$
--
--   The two quadratic factors are coprime, and each has greatest common divisor with $y^{2}-1$ dividing $3$; since $3$ cannot divide both, one of them is coprime to the remaining product and must be a perfect square. That is impossible because $y^{2} < y^{2}+y+1 < (y+1)^{2}$ and $(y-1)^{2} < y^{2}-y+1 < y^{2}$.
-- source:
--   Consequence of the Dris parametrisation of an odd perfect number in Euler form; see J. A. B. Dris, 'The abundancy index of divisors of odd perfect numbers', Journal of Integer Sequences 15 (2012), Article 12.4.4, Section 2 (the relations sigma(p^k)/2 | m^2 and p^k | sigma(m^2)). The Diophantine statement itself is elementary.

import Mathlib
open Finset

namespace OddPerfectNumber

theorem sigma_prime_pow_ne_two_mul_sq_of_six_dvd (p k m : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : (k + 1) % 6 = 0) :
    (∑ d ∈ (p ^ k).divisors, d) ≠ 2 * m ^ 2 := by sorry

end OddPerfectNumber
