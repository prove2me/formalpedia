-- Prove2me | Theorems.Thm_OddPerfectNumber_order_five_phi5_factor_pair
-- name    : OddPerfectNumber.order_five_phi5_factor_pair
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T18:26:04.217273+00:00
-- url     : https://prove2.me/theorems/8812475b-b166-4369-843b-4410ce99ac1e
-- title:
--   Order five forces the Phi_5 factor pair (qk - 1)(qz - 1) with p + 1 = qk
-- statement:
--   Let p be a prime with p ≡ 1 mod 4, let q be an odd prime with q | (p+1)/2, and suppose ord_p(q) = 5. Write k = (p+1)/q, so that p + 1 = qk and p = qk - 1. Then there is a positive integer z with Phi_5(q) = q^4 + q^3 + q^2 + q + 1 = (qk - 1)(qz - 1). Proof: p | Phi_5(q); writing Phi_5(q) = pU, reducing modulo q gives p ≡ -1 and Phi_5(q) ≡ 1, hence U ≡ -1 mod q, so q | U + 1 and U = qz - 1 for a positive z. This is the Section 21 factor-pair reduction. Published as an Open research child; no proof is asserted by this submission.
-- source:
--   Section 21 of artifacts/opn/OPN_LIVE_STATE_2026-09-17.md. Composes the newly published child OddPerfectNumber.order_five_phi5_dvd with the divisibility q | p + 1 derived from q | (p+1)/2 and p % 4 = 1 (p + 1 = 2 * ((p+1)/2)). No BCR, no valuation gap, no IsSquare, no reciprocity.

import Mathlib

namespace OddPerfectNumber

theorem order_five_phi5_factor_pair (p q : Nat)
    (hp : p.Prime)
    (hp4 : p % 4 = 1)
    (hq : q.Prime)
    (hqt : q ∣ (p + 1) / 2)
    (h5 : orderOf (q : ZMod p) = 5) :
    ∃ k z : Nat,
      p + 1 = q * k ∧ 0 < z ∧
        q ^ 4 + q ^ 3 + q ^ 2 + q + 1 = (q * k - 1) * (q * z - 1) := by
  sorry

end OddPerfectNumber
