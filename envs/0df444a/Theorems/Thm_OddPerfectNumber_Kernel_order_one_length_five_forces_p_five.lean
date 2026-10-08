-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_order_one_length_five_forces_p_five
-- name    : OddPerfectNumber.Kernel.order_one_length_five_forces_p_five
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T07:01:55.607971+00:00
-- url     : https://prove2.me/theorems/df0fc021-7d64-4c72-a1a2-7f79c03a6034
-- title:
--   An order-one length-five source forces the Euler prime to be five
-- statement:
--   For a prime p, if q is congruent to one modulo p and p divides the length-five geometric sum 1+q+q^2+q^3+q^4, then p=5. The sum is congruent to 5 modulo p, so p divides 5.
-- source:
--   Elementary geometric-sum congruence used in the e_q=2 middle-source branch of the k=5 Odd Perfect Number residual.

import Mathlib

import Mathlib

namespace OddPerfectNumber.Kernel

theorem order_one_length_five_forces_p_five (p q : Nat) (hp : p.Prime)
    (hqmod : q % p = 1)
    (hsrc : p ∣ ∑ i ∈ Finset.range 5, q ^ i) :
    p = 5 := by
  sorry

end OddPerfectNumber.Kernel
