-- Prove2me | Theorems.Thm_OddPerfectNumber_order_five_vieta_divisibility
-- name    : OddPerfectNumber.order_five_vieta_divisibility
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T18:26:53.925876+00:00
-- url     : https://prove2.me/theorems/05548178-ac78-4af3-8dc8-6f27c31a8632
-- title:
--   Order five Vieta divisibility: p | q^2 + q + k^2 + k + 1
-- statement:
--   Let p be prime, p + 1 = q k, and ord_p(q) = 5. Then p divides the Vieta expression q^2 + q + k^2 + k + 1. Proof: q k ≡ 1 modulo p, so q^2 k^2 ≡ 1 and q^2 k ≡ q; multiplying the Vieta expression by q^2 therefore gives q^4 + q^3 + 1 + q + q^2 = Phi_5(q) ≡ 0 modulo p. Since p is prime and q is a unit modulo p, q^2 is invertible and the expression itself is 0 modulo p. This is the Section 21 Vieta jumping entry point. Published as an Open research child; no proof is asserted by this submission.
-- source:
--   Section 21 of artifacts/opn/OPN_LIVE_STATE_2026-09-17.md. Composes the newly published child OddPerfectNumber.order_five_phi5_dvd with the modular identity q k ≡ 1 coming from p + 1 = q k. No BCR, no valuation gap, no IsSquare, no reciprocity.

import Mathlib

namespace OddPerfectNumber

theorem order_five_vieta_divisibility (p q k : Nat)
    (hp : p.Prime)
    (hpk : p + 1 = q * k)
    (h5 : orderOf (q : ZMod p) = 5) :
    p ∣ q ^ 2 + q + k ^ 2 + k + 1 := by
  sorry

end OddPerfectNumber
