-- Prove2me | Theorems.Thm_OddPerfectNumber_no_dris_square_index_of_exp_ne_one_mod_sixteen
-- name    : OddPerfectNumber.no_dris_square_index_of_exp_ne_one_mod_sixteen
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-11T19:17:59.465458+00:00
-- url     : https://prove2.me/theorems/42183098-e33c-4610-9367-0fa4863ad8fe
-- title:
--   No square Dris index unless $k \\equiv 1 \\pmod{16}$
-- statement:
--   Let $p$ be a prime with $p \equiv 1 \pmod 4$, let $k \equiv 1 \pmod 4$ with $k \not\equiv 1 \pmod{16}$, and let $m$ be odd. Then the Dris relations
--
--   $$2m^2 = \sigma(p^k)\,s, \qquad \sigma(m^2) = p^k s$$
--
--   cannot hold with an index $s$ that is a perfect square. In particular there is no square Dris index at the special exponents $k = 5, 9, 13$.
--
--   Indeed, if $s = u^2$ then $u^2 \mid m^2$ (the index divides $m^2$ because it is odd and divides $2m^2$), so $u \mid m$; writing $m = uw$ and cancelling $u^2$ from the first relation turns it into $\sigma(p^k) = 2w^2$. It is known that a solution of $\sigma(p^k) = 2w^2$ with $p$ prime, $p \equiv k \equiv 1 \pmod 4$ forces $p \equiv k \equiv 1 \pmod{16}$, which contradicts $k \not\equiv 1 \pmod{16}$.
-- source:
--   Consequence of the mod-16 theorem for the equation sigma(p^k) = 2 w^2 (platform theorem OddPerfectNumber.prime_and_exp_mod_sixteen_of_sigma_eq_two_mul_sq) applied to the Dris parametrisation of J. A. B. Dris, Journal of Integer Sequences 15 (2012), Article 12.4.4.

import Mathlib
open Finset

namespace OddPerfectNumber

theorem no_dris_square_index_of_exp_ne_one_mod_sixteen (p k m s u : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk16 : k % 16 ≠ 1) (hm : Odd m)
    (hsq : s = u ^ 2) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ x ∈ (m ^ 2).divisors, x) = p ^ k * s) := by
  sorry

end OddPerfectNumber
