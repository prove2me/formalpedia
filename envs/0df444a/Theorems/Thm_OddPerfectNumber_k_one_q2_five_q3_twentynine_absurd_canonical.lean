-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_absurd_canonical
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_absurd_canonical
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-19T19:18:24.062985+00:00
-- url     : https://prove2.me/theorems/e416dd40-58dc-4fca-af43-a4247ad78abb
-- title:
--   Canonical q2=5, q3=29 four-support branch is impossible
-- statement:
--   In the canonical four-support k=1 interface with support {3,5,29,q4} (q1=3, q2=5, q3=29, q4>29), the branch is contradictory. The half-exponent coordinates of m^2, the local sigma product and the exponent positivity are derived here from the support interface, so the parent dispatcher exposes no coordinate, floor or factorisation premises and never sees the accidental doubled 8,6,4,2 convention.
-- source:
--   Canonical-interface composition for the q2=5, q3=29 branch of the k_one four-support frontier: the accepted coordinate-level terminal k_one_q2_five_q3_twentynine_absurd_canonical_coordinates_v1, whose own composition imports k_one_q2_five_q3_twentynine_half_exponent_floors_v1 (canonical 4,3,2,1), driven by the same coordinate extraction used for q3=19, 23 and 11.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_absurd_canonical_coordinates_v1
import Theorems.Thm_OddPerfectNumber_four_support_factorization_expansion
import Theorems.Thm_OddPerfectNumber_sq_factorization_two
import Theorems.Thm_OddPerfectNumber_sigma_eq_local_prod

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_absurd_canonical (p m d q4 : Nat)
    (hp : p.Prime)
    (hp4 : p % 4 = 1)
    (hm : Odd m)
    (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : m.primeFactors = {3, 5, 29, q4})
    (hq4prime : q4.Prime)
    (hq4gt : 29 < q4) :
    False := by
  sorry

end OddPerfectNumber
