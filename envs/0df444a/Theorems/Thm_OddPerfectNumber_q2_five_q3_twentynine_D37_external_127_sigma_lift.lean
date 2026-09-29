-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D37_external_127_sigma_lift
-- name    : OddPerfectNumber.q2_five_q3_twentynine_D37_external_127_sigma_lift
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T08:12:03.032623+00:00
-- url     : https://prove2.me/theorems/1af7088a-615d-40cd-82f2-f3677d6ef116
-- title:
--   Lift the D=37 local 127 source into sigma
-- statement:
--   A 127 divisor of the q4=37 local sigma factor divides the full four-factor sigma product.
-- source:
--   Rewrite sigma by its factorization and lift the local divisibility through multiplication.

import Mathlib

namespace OddPerfectNumber

theorem q2_five_q3_twentynine_D37_external_127_sigma_lift (sigma a b c e : Nat) (hsigma : sigma = (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2 * c + 1), 29 ^ i) * (∑ i ∈ Finset.range (2 * e + 1), 37 ^ i)) (hlocal : 127 ∣ ∑ i ∈ Finset.range (2 * e + 1), 37 ^ i) : 127 ∣ sigma := by
  sorry

end OddPerfectNumber
