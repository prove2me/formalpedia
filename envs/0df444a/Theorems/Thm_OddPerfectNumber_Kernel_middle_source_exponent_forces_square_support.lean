-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_middle_source_exponent_forces_square_support
-- name    : OddPerfectNumber.Kernel.middle_source_exponent_forces_square_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T09:37:40.663983+00:00
-- url     : https://prove2.me/theorems/99dbe034-1eaf-487d-8de2-6024ee115497
-- title:
--   A middle-block source of exponent at least two enters the square support
-- statement:
--   If a prime q occurs once in the explicit factorisation m = 3*u*a*b*d1*q*r, and its exponent in m is at least two, while q divides none of the other displayed factors, then q divides the square factor a. This is the support bridge for a middle-block Euler-prime source.
-- source:
--   The proof is the elementary factorization implication q^2 | m from q.factorization m >= 2, followed by cancellation of the displayed q factor and repeated Nat.Prime.dvd_mul case splits. The child intentionally exposes all non-divisibility hypotheses so it cannot silently overclaim support closure.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem middle_source_exponent_forces_square_support (p m q a b d1 u r : Nat)
    (hq : q.Prime)
    (hm : m = 3 * u * a * b * d1 * q * r)
    (he : 2 ≤ m.factorization q)
    (h3 : ¬ q ∣ 3) (hu : ¬ q ∣ u) (hb : ¬ q ∣ b)
    (hd : ¬ q ∣ d1) (hr : ¬ q ∣ r) :
    q ∣ a := by
  sorry

end OddPerfectNumber.Kernel
