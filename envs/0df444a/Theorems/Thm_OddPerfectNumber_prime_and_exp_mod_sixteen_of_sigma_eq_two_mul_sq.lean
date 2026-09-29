-- Prove2me | Theorems.Thm_OddPerfectNumber_prime_and_exp_mod_sixteen_of_sigma_eq_two_mul_sq
-- name    : OddPerfectNumber.prime_and_exp_mod_sixteen_of_sigma_eq_two_mul_sq
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-08T21:05:23.694427+00:00
-- url     : https://prove2.me/theorems/f4bdb9fa-b658-4f53-84f4-e27032b2cb34
-- title:
--   $\sigma(p^k) = 2m^2$ forces $p \equiv k \equiv 1 \pmod{16}$
-- statement:
--   Write $\sigma(n)=\sum_{d\mid n} d$ for the sum-of-divisors function.
--
--   Let $p$ be a prime with $p \equiv 1 \pmod 4$ and let $k$ be a natural number with $k \equiv 1 \pmod 4$. If
--
--   $$\sigma(p^{k}) \;=\; 2m^{2}$$
--
--   for some natural number $m$, then necessarily
--
--   $$p \equiv 1 \pmod{16} \qquad\text{and}\qquad k \equiv 1 \pmod{16}.$$
--
--   The statement is not vacuous: for $p = 17$ and $k = 1$ one has $\sigma(17) = 18 = 2\cdot 3^{2}$, and indeed $17 \equiv 1 \pmod{16}$ and $1 \equiv 1 \pmod{16}$; likewise $\sigma(97) = 98 = 2 \cdot 7^{2}$ with $97 \equiv 1 \pmod{16}$.
--
--   **Role in the theory of odd perfect numbers.** If $N = p^{k}m^{2}$ is an odd perfect number in Euler form, so that $p \equiv k \equiv 1 \pmod 4$ and $p \nmid m$, the Euler equation $\sigma(p^{k})\sigma(m^{2}) = 2p^{k}m^{2}$ together with $p \nmid \sigma(p^{k})$ yields natural numbers $s$ with $2m^{2} = \sigma(p^{k})s$ and $\sigma(m^{2}) = p^{k}s$. One has $s = 1$ exactly in the extremal situation $m^{2} \le p^{k}$, and then $\sigma(p^{k}) = 2m^{2}$. The congruences above therefore restrict that extremal situation severely: unless both the special prime and the special exponent are $\equiv 1 \pmod{16}$, one must have $p^{k} < m^{2}$.
-- source:
--   Elementary consequence of the classical splitting of the Euler equation for odd perfect numbers; the parametrisation 2m^2 = sigma(p^k) s, sigma(m^2) = p^k s is due to J. A. B. Dris, 'The abundancy index of divisors of odd perfect numbers', Journal of Integer Sequences 15 (2012), Article 12.4.4, Section 2.

import Mathlib
open Finset

namespace OddPerfectNumber

theorem prime_and_exp_mod_sixteen_of_sigma_eq_two_mul_sq (p k m : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 1) (hk : k % 4 = 1)
    (h : (∑ d ∈ (p ^ k).divisors, d) = 2 * m ^ 2) :
    p % 16 = 1 ∧ k % 16 = 1 := by sorry

end OddPerfectNumber
