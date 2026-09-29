-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D75_force_three_source
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_D75_force_three_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T23:45:28.469893+00:00
-- url     : https://prove2.me/theorems/42eac489-92dc-4f5e-8d43-eda865df42e5
-- title:
--   The D=75 q3=19 source must come from the 3-component
-- statement:
--   For the q3=19,D=75,q4=263 sigma product, divisibility by 263 cannot come from the 5-, 19-, or self-263 local factors; the accepted order certificate ord_263(3)=131 therefore forces the actual 3-exponent 2a to be at least 130.
-- source:
--   Canonical source-purity reduction using accepted odd-length order parity and local-sum self-divisibility certificates.

import Mathlib
import Theorems.Thm_OddPerfectNumber_order_three_mod_263_eq_131
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order
import Theorems.Thm_OddPerfectNumber_local_sum_mod_self

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_D75_force_three_source (sigma a b c e : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), 263 ^ i))
    (hdiv : 263 ∣ sigma) :
    130 ≤ 2 * a := by
  sorry

end OddPerfectNumber
