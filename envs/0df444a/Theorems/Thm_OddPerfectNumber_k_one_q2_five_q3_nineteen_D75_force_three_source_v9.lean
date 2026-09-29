-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D75_force_three_source_v9
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_D75_force_three_source_v9
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T00:20:02.02544+00:00
-- url     : https://prove2.me/theorems/17cb8d8b-2e89-4c45-8bf0-ff70376ffa4c
-- title:
--   The D=75 q3=19 source must come from the 3-component (v9)
-- statement:
--   For the q3=19,D=75,q4=263 sigma product, divisibility by 263 cannot come from the 5-, 19-, or self-263 local factors; ord_263(3)=131 therefore forces the actual 3-exponent 2a to be at least 130.
-- source:
--   Changed v9 source-purity reduction: the closed modular-power decision proofs use a bounded maxRecDepth together with the remote free-variable revert hint.

import Mathlib
import Theorems.Thm_OddPerfectNumber_order_three_mod_263_eq_131
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order
import Theorems.Thm_OddPerfectNumber_local_sum_mod_self

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_D75_force_three_source_v9 (sigma a b c e : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), 263 ^ i))
    (hdiv : 263 ∣ sigma) :
    130 ≤ 2 * a := by
  sorry

end OddPerfectNumber
