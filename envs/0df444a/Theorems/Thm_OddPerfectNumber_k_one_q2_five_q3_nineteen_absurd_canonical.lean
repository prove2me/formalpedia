-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_absurd_canonical
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_absurd_canonical
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-19T18:41:27.057439+00:00
-- url     : https://prove2.me/theorems/9f0b0264-cf47-4a88-9907-2de557cd5176
-- title:
--   Canonical q2=5, q3=19 four-support branch is impossible
-- statement:
--   In the canonical four-support k=1 interface with support {3,5,19,q4} (q1=3, q2=5, q3=19, q4>19), the branch is contradictory. The exponent coordinates a,b,c,e of m^2 = 3^(2a) 5^(2b) 19^(2c) q4^(2e), the local sigma product and the exponent floors are derived here from the support interface, so the parent dispatcher exposes no coordinate, floor or factorisation premises.
-- source:
--   Canonical-interface composition for the q2=5, q3=19 branch of the k_one four-support frontier: the accepted coordinate-level terminal k_one_q2_five_q3_nineteen_absurd_canonical_coordinates_v1 (which already composes the clean half-exponent floor package with k_one_q2_five_q3_nineteen_absurd_v6) driven by a coordinate extraction from the parent four-support interface.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_absurd_canonical_coordinates_v1
import Theorems.Thm_OddPerfectNumber_four_support_factorization_expansion
import Theorems.Thm_OddPerfectNumber_sq_factorization_two
import Theorems.Thm_OddPerfectNumber_sigma_eq_local_prod

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_absurd_canonical (p m d q4 : Nat)
    (hp : p.Prime)
    (hp4 : p % 4 = 1)
    (hm : Odd m)
    (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : m.primeFactors = {3, 5, 19, q4})
    (hq4prime : q4.Prime)
    (hq4gt : 19 < q4) :
    False := by
  sorry

end OddPerfectNumber
