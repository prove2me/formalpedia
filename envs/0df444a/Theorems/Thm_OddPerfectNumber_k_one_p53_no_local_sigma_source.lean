-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_p53_no_local_sigma_source
-- name    : OddPerfectNumber.k_one_p53_no_local_sigma_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T04:34:26.539387+00:00
-- url     : https://prove2.me/theorems/b1344799-a124-4651-983b-0db22e6768c4
-- title:
--   The p=53 sigma product has no local source when all four orders are even
-- statement:
--   If all four local odd-length sigma factors for bases 3, 5, 23 and 691 have even order modulo 53, then 53 cannot divide their product.
-- source:
--   Apply the accepted even-order obstruction to each factor and split primality across the product.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order

namespace OddPerfectNumber

theorem k_one_p53_no_local_sigma_source (sigma a b c e : Nat)
    (hsigma : sigma = (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2 * c + 1), 23 ^ i) * (∑ i ∈ Finset.range (2 * e + 1), 691 ^ i))
    (hdiv : 53 ∣ sigma)
    (h3 : Even (orderOf (3 : ZMod 53)))
    (h5 : Even (orderOf (5 : ZMod 53)))
    (h23 : Even (orderOf (23 : ZMod 53)))
    (h691 : Even (orderOf (691 : ZMod 53))) :
    False := by
  sorry

end OddPerfectNumber
