-- Prove2me | Theorems.Thm_OddPerfectNumber_orderOf_three_eq_prime_index
-- name    : OddPerfectNumber.orderOf_three_eq_prime_index
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-19T20:47:13.397234+00:00
-- url     : https://prove2.me/theorems/71718927-26f7-4fdf-b63f-1d0ef87c9440
-- title:
--   Divisibility of the base-3 geometric sum by q4 forces the order to be the odd index
-- statement:
--   If an odd prime q4 (not 2) divides the base-3 geometric sum S_3(2e+1) = 1 + 3 + ... + 3^(2e) and the odd index 2e+1 is prime, then the multiplicative order of 3 modulo q4 equals that index. This is the elementary index bridge used to convert a pure q4-power local sigma factor into a prime-order statement: q4 | S_3(t) gives 3^t = 1 mod q4, the order divides the prime t, and order 1 would force q4 | 2.
-- source:
--   Elementary index step described in the q3=31 and 37<=q3<=61 four-support branch analyses: a pure q4-power equality of the 3-component sigma factor forces orderOf (3 : ZMod q4) to be the prime index. Reuses the accepted OddPerfectNumber.geom_sum_dvd_implies_zmod_pow_eq_one bridge and Mathlib's orderOf_eq_prime.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_dvd_implies_zmod_pow_eq_one

namespace OddPerfectNumber

theorem orderOf_three_eq_prime_index (q4 e : Nat)
    (hq4 : q4.Prime)
    (hq4ne2 : q4 ≠ 2)
    (hprime : (2 * e + 1).Prime)
    (hdiv : q4 ∣ ∑ i ∈ Finset.range (2 * e + 1), 3 ^ i) :
    orderOf (3 : ZMod q4) = 2 * e + 1 := by
  sorry

end OddPerfectNumber
