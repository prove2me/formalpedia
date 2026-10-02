-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_odd_index_prime_mod_twenty_four
-- name    : OddPerfectNumber.Kernel.five_odd_index_prime_mod_twenty_four
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-02T09:26:26.036786+00:00
-- url     : https://prove2.me/theorems/3d16e812-9942-4647-b9fd-4c6ef11ed954
-- title:
--   Each index prime is $7 \pmod{24}$
-- statement:
--   In the $k=5$ two-prime residual the odd-multiplicity prime of each cyclotomic block is one of the two square-free index primes $q, r$. This lemma transfers the block's congruence information onto that prime.
--
--   Suppose a block $N$ satisfies $N \equiv 7 \pmod 8$ and $N = q a^2$ with $a$ odd. Since $a$ is odd, $a^2 \equiv 1 \pmod 8$, so
--
--   $$q \equiv N \cdot (a^2)^{-1} \equiv 7 \cdot 1 \equiv 7 \pmod 8.$$
--
--   Modulo $3$ the situation is different only in that one must exclude $3 \mid a$. Here $N \equiv 1 \pmod 3$, so $3 \nmid N = q a^2$, which forces $3 \nmid a$ and hence $a^2 \equiv 1 \pmod 3$; therefore $q \equiv 1 \pmod 3$.
--
--   Solving the pair of congruences $q \equiv 7 \pmod 8$ and $q \equiv 1 \pmod 3$ gives $q \equiv 7 \pmod{24}$.
--
--   **Consequence.** Applied to both cyclotomic blocks this pins both index primes: $q \equiv r \equiv 7 \pmod{24}$. Each is therefore a quadratic **non**-residue modulo $4$-residue pair, and in particular $q \equiv r \equiv 3 \pmod 4$, which is exactly the shape that makes them unusable as incoming $\sigma$-sources for the Euler prime.
-- source:
--   Odd Perfect Number Conjecture mission, k=5 Dris branch; combines the modulo-8 and modulo-3 transfers of the square factor a^2. Mission research note of 2026-10-02.

import Mathlib

namespace OddPerfectNumber.Kernel

/-- If an odd index prime `q` is the odd-multiplicity factor of a cyclotomic block that is
`7 (mod 8)`, and that block is `1 (mod 3)`, then `q = 7 (mod 24)`. -/
theorem five_odd_index_prime_mod_twenty_four (N q a : Nat)
    (hN8 : N % 8 = 7) (hfactor : N = q * a ^ 2) (ha : Odd a)
    (hN3 : N % 3 = 1) :
    q % 24 = 7 := by
  sorry

end OddPerfectNumber.Kernel
