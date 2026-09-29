-- Prove2me | Theorems.Thm_OddPerfectNumber_q_mod_four_eq_one_of_q_dvd_half_successor
-- name    : OddPerfectNumber.q_mod_four_eq_one_of_q_dvd_half_successor
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-19T00:45:55.766201+00:00
-- url     : https://prove2.me/theorems/0142d099-42f4-4900-90a5-ecaf8ee071e8
-- title:
--   Branch-I congruence: q | (p+1)/2 with p square mod q forces q = 1 mod 4
-- statement:
--   If p = 1 mod 4, q is prime, p is a square mod q, and q divides (p+1)/2, then q = 1 mod 4. Proof: (p+1)/2 doubling gives q | p+1 so p = -1 in ZMod q; IsSquare transports to IsSquare (-1); ZMod.exists_sq_eq_neg_one_iff excludes q = 3 mod 4; q odd excludes 2. Published as an Open research child; no proof is asserted by this submission.
-- source:
--   Branch-I Section 16.1 of artifacts/opn/OPN_LIVE_STATE_2026-09-17.md. Cheap formal congruence; reuses hsqP already present in k_one_endgame_q_dvd_d.

import Mathlib

namespace OddPerfectNumber

theorem q_mod_four_eq_one_of_q_dvd_half_successor (p q : Nat)
    (hp4 : p % 4 = 1)
    (hq : q.Prime)
    (hsqP : IsSquare (p : ZMod q))
    (hqt : q ∣ (p + 1) / 2) :
    q % 4 = 1 := by
  sorry

end OddPerfectNumber
