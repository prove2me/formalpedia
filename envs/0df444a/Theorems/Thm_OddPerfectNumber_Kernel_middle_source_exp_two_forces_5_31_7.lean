-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_middle_source_exp_two_forces_5_31_7
-- name    : OddPerfectNumber.Kernel.middle_source_exp_two_forces_5_31_7
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T07:42:14.242985+00:00
-- url     : https://prove2.me/theorems/d8e40da1-1f71-407b-ab46-7c8f59968048
-- title:
--   An order-one exponent-two middle source forces the explicit k=5 tuple
-- statement:
--   In the normalized k=5 two-prime branch, if the middle-block prime qC has exponent two in m and is an order-one incoming source for p, then the order-one length-five restriction gives p=5; the two normalized cyclotomic equations then force qC=31, qD=7 and square factors a=b=1.
-- source:
--   Elementary specialization of the accepted order-one length-five source reduction and the normalized k=5 block equations. This isolates the explicit (p,qC,qD)=(5,31,7) residual for the second-Dris contradiction.

import Mathlib

import Mathlib

namespace OddPerfectNumber.Kernel

theorem middle_source_exp_two_forces_5_31_7 (p qC qD a b u : Nat)
    (hp : p.Prime)
    (hu : p + 1 = 6 * u ^ 2)
    (hC : p ^ 2 + p + 1 = qC * a ^ 2)
    (hD : p ^ 2 - p + 1 = 3 * (qD * b ^ 2))
    (hqC : qC.Prime)
    (hqD : qD.Prime)
    (hqCmod : qC % p = 1)
    (hsource : p ∣ ∑ i ∈ Finset.range 5, qC ^ i) :
    p = 5 ∧ qC = 31 ∧ qD = 7 ∧ a = 1 ∧ b = 1 := by
  sorry

end OddPerfectNumber.Kernel
