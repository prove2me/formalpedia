-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_p1709_no_local_sigma_source
-- name    : OddPerfectNumber.k_one_p1709_no_local_sigma_source
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-14T04:11:57.054371+00:00
-- url     : https://prove2.me/theorems/eda319a9-834a-4c49-a94c-59653b5d9c09
-- title:
--   The p=1709 sigma product has no local source when all four orders are even
-- statement:
--   If the four local sigma factors for bases 3, 5, 19 and 101 all have even multiplicative order modulo 1709, none is divisible by 1709; primality of 1709 then contradicts 1709 dividing their product.
-- source:
--   Apply the accepted even-order geometric-sum obstruction to each factor and split prime divisibility across the product.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order

namespace OddPerfectNumber

theorem k_one_p1709_no_local_sigma_source (sigma a b c e : Nat)
    (hsigma : sigma = (∑ i ∈ Finset.range (a + 1), 3 ^ i) * (∑ i ∈ Finset.range (b + 1), 5 ^ i) * (∑ i ∈ Finset.range (c + 1), 19 ^ i) * (∑ i ∈ Finset.range (e + 1), 101 ^ i))
    (hdiv : 1709 ∣ sigma)
    (h3 : Even (orderOf (3 : ZMod 1709)))
    (h5 : Even (orderOf (5 : ZMod 1709)))
    (h19 : Even (orderOf (19 : ZMod 1709)))
    (h101 : Even (orderOf (101 : ZMod 1709))) :
    False := by
  sorry

end OddPerfectNumber
