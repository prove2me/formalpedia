-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_odd_p_source_is_middle_block_or_square_part
-- name    : OddPerfectNumber.Kernel.odd_p_source_is_middle_block_or_square_part
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T21:12:56.834192+00:00
-- url     : https://prove2.me/theorems/7ab1fdad-00da-45c8-b5e2-d25fa210a8f3
-- title:
--   An odd-multiplicity incoming sigma source of the Euler prime lies in the middle block or the square part
-- statement:
--   Let m = 3*u*a*b*d1*q*r be the shape forced in the two-prime k=5 branch, and let t be a prime dividing m. Then t = 3, or t = q, or t = r, or t divides the square part u*a*b*d1. Excluding t = 3 (3 is a quadratic nonresidue modulo p, so an incoming source of p has odd order and cannot be 3) and t = r (the minus-block index prime is a nonresidue modulo p, hence likewise excluded), the incoming sigma source of the Euler prime must be the middle-block index prime q, or a prime dividing the square part u*a*b*d1. This localises the odd-multiplicity incoming p-source to two explicit cases and is the step the valuation budget needs.
-- source:
--   Pure prime-support splitting, proved by Nat.Prime.dvd_mul applied repeatedly to the Proved shape theorem five_two_prime_kernel_explicit_m (223c7991). With m = 3*(u*a*b*d1)*(q*r) and t.Prime with t | m, Euclid's lemma gives t | 3, or t | u*a*b*d1, or t | q, or t | r; primality of t then converts each divisibility into the corresponding disjunction, and the hypotheses ht3, htr remove the 3 and r branches. No cyclotomic or valuation theory is needed here: the exclusion of 3 and of r as incoming sigma sources is proved separately by three_is_quadratic_nonresidue_mod_euler_prime (f113d40e) and odd_order_source_not_minus_block_prime (240feedb), and is consumed by the parent. This statement deliberately does NOT assert t != q, unlike the malformed and Disproved target five_odd_p_source_is_middle_or_square_part (7d5867b0), which assumed t != q while concluding t = q.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem odd_p_source_is_middle_block_or_square_part
    {p m u a b d1 q r t : Nat}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (ht : t.Prime) (htd : Dvd.dvd t m)
    (hshape : m = 3 * u * a * b * d1 * q * r)
    (ht3 : t != 3) (htr : t != r) :
    t = q \/ Dvd.dvd t (u * a * b * d1) := by sorry

end OddPerfectNumber.Kernel
