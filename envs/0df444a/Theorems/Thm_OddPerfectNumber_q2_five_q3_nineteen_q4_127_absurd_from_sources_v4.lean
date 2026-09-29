-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_absurd_from_sources_v4
-- name    : OddPerfectNumber.q2_five_q3_nineteen_q4_127_absurd_from_sources_v4
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T02:10:04.565546+00:00
-- url     : https://prove2.me/theorems/2d651695-ab29-4b9b-a406-a2d5cd6d41c0
-- title:
--   The q4=127 source certificate is contradictory
-- statement:
--   The accepted small-D five-divisibility bridge contradicts the accepted q4=127 local product no-five certificate when the three non-5 sources are excluded.
-- source:
--   Compose the two independently accepted q4=127 certificates without importing any Open parent.

import Mathlib
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_five_dvd_sigma_v4
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_product_no_five

namespace OddPerfectNumber

theorem q2_five_q3_nineteen_q4_127_absurd_from_sources_v4 (p m d sigma a b c e : Nat)
    (hp : p.Prime)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsigma : sigma = p * d)
    (hD : (p + 1) / 2 < 185)
    (hpow : 5 ^ 6 ∣ m ^ 2)
    (hlocal : sigma =
      (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (e + 1), 127 ^ i))
    (h3 : ¬ 5 ∣ ∑ i ∈ Finset.range (a + 1), 3 ^ i)
    (h19 : ¬ 5 ∣ ∑ i ∈ Finset.range (c + 1), 19 ^ i)
    (h127 : ¬ 5 ∣ ∑ i ∈ Finset.range (e + 1), 127 ^ i) :
    False := by
  sorry

end OddPerfectNumber
