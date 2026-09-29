-- Prove2me | Theorems.Thm_OddPerfectNumber_order_five_reciprocal_phi5_dvd
-- name    : OddPerfectNumber.order_five_reciprocal_phi5_dvd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T18:26:25.616292+00:00
-- url     : https://prove2.me/theorems/67d6a07f-4446-48e1-9d91-aaf4b351f465
-- title:
--   Order five: the reciprocal root k of q k = p + 1 also satisfies p | Phi_5(k)
-- statement:
--   Let p be prime and suppose p + 1 = q k for natural numbers q and k, with ord_p(q) = 5. Then p divides Phi_5(k) = k^4 + k^3 + k^2 + k + 1. Indeed q k ≡ 1 modulo p, so k is the inverse of q modulo p and inherits k^5 = 1; the same telescoping argument applied at k (using k not congruent to 1 modulo p, since otherwise q would equal 1 modulo p and have order 1) gives p | k^5 - 1 = (k - 1) Phi_5(k). This is the reciprocal-root half of the Section 16.1 structure. Published as an Open research child; no proof is asserted by this submission.
-- source:
--   Section 16.1 of artifacts/opn/OPN_LIVE_STATE_2026-09-17.md. Uses the Proved helper OddPerfectNumber.geom_mul_sub_one (node 069159f8-59c6-4023-af9d-5ad6dabcdf1b) and the Proved Nat/ZMod bridge OddPerfectNumber.zmod_pow_eq_one_iff (node 890d5806-d6f3-4d4c-8ec3-42d96f9b4165). No BCR, no valuation gap, no IsSquare, no reciprocity.

import Mathlib

namespace OddPerfectNumber

theorem order_five_reciprocal_phi5_dvd (p q k : Nat)
    (hp : p.Prime)
    (hpk : p + 1 = q * k)
    (h5 : orderOf (q : ZMod p) = 5) :
    p ∣ k ^ 4 + k ^ 3 + k ^ 2 + k + 1 := by
  sorry

end OddPerfectNumber
