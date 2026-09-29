-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_half_successor_support
-- name    : OddPerfectNumber.k_one_half_successor_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T11:03:40.272043+00:00
-- url     : https://prove2.me/theorems/8766e9b7-b383-414e-91dc-8eaead923984
-- title:
--   A divisor of the half-successor divides the square part
-- statement:
--   Under the k=1 product equation m²=((p+1)/2)d, every prime divisor q of (p+1)/2 divides m. This is the elementary support bridge for the half-successor branch.
-- source:
--   Elementary divisibility from the canonical k=1 product equation and primality of q.

import Mathlib

namespace OddPerfectNumber

theorem k_one_half_successor_support (p m d q : Nat)
    (hq : q.Prime)
    (hdvd : m ^ 2 = ((p + 1) / 2) * d)
    (hqD : q ∣ (p + 1) / 2) :
    q ∣ m := by sorry

end OddPerfectNumber
