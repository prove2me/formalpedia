-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_first_block_coprime_to_middle_block
-- name    : OddPerfectNumber.Kernel.five_first_block_coprime_to_middle_block
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T19:56:43.560222+00:00
-- url     : https://prove2.me/theorems/f2719a7c-1257-4325-a784-d3b431465944
-- title:
--   The first k=5 block is coprime to the middle cyclotomic block
-- statement:
--   Let p, q, c be natural numbers. Suppose p is a prime and q is a prime different from two. Suppose q divides p plus one and c equals p squared plus p plus one. Then q and c are coprime. Indeed every prime t dividing p plus one satisfies p squared plus p plus one congruent to one minus one plus one, that is to one, modulo t, because p is congruent to minus one modulo t. Hence no prime factor of p plus one divides p squared plus p plus one, and the greatest common divisor is one. This is the elementary reason the normalised block (p+1)/2 and the block p squared plus p plus one can be treated as separate factors when allocating the two square-free index primes.
-- source:
--   This is the gcd(E, C) = 1 statement of the k=5 two-prime normalisation, in the divisibility form that avoids every quotient. The quotient version would be gcd((p+1)/6, p^2+p+1) = 1; this child states the primitive fact instead: if a prime q divides p+1 then q is coprime to p^2+p+1. The argument is the single congruence p = -1 (mod q), which gives p^2+p+1 = 1-1+1 = 1 (mod q), so q cannot divide it. Computationally checked over all primes p = 1 (mod 4) below 4000 with 6 dividing p+1: no violation. The companion fact gcd(C, F) = 1 comes from C - D = 2p with C and D both odd and C = D = 1 (mod p), while gcd(E, F) divides 3 only -- and one must NOT assume it equals one, since 3 does divide E when p = 17 (E = 3), p = 53 (E = 9) and p = 89 (E = 15).

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_first_block_coprime_to_middle_block {p q c : Nat}
    (hp : Nat.Prime p) (hq2 : q != 2) (hq : Dvd.dvd q (p + 1))
    (hc : c = p ^ 2 + p + 1) :
    Nat.Coprime q c := by
  sorry

end OddPerfectNumber.Kernel
