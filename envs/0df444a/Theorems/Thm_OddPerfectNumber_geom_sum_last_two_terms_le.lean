-- Prove2me | Theorems.Thm_OddPerfectNumber_geom_sum_last_two_terms_le
-- name    : OddPerfectNumber.geom_sum_last_two_terms_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T01:12:23.726575+00:00
-- url     : https://prove2.me/theorems/4e11e5ee-ffa0-4493-aebc-bc7a43d61160
-- title:
--   The last two powers are bounded by their geometric sum
-- statement:
--   For a positive exponent, the final two powers occur in the finite geometric sum, giving an exact lower bound useful in abundance certificates.
-- source:
--   Elementary finite-sum decomposition; this helper is used to strengthen q4 local abundance bounds in the q3=13 middle candidate certificate.

import Mathlib

namespace OddPerfectNumber

theorem geom_sum_last_two_terms_le (q e : Nat) (he : 1 ≤ e) :
    q ^ e + q ^ (e - 1) ≤ ∑ i ∈ Finset.range (e + 1), q ^ i := by
  sorry

end OddPerfectNumber
