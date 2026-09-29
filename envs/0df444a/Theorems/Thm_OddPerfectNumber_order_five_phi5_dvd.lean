-- Prove2me | Theorems.Thm_OddPerfectNumber_order_five_phi5_dvd
-- name    : OddPerfectNumber.order_five_phi5_dvd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T18:25:43.86943+00:00
-- url     : https://prove2.me/theorems/d6f594f2-42d5-4de4-bdf3-f0e1b1b2ecea
-- title:
--   Order five forces p to divide Phi_5(q) = q^4 + q^3 + q^2 + q + 1
-- statement:
--   Let p and q be primes and suppose the multiplicative order of q modulo p is exactly 5. Then p divides the fifth cyclotomic polynomial value Phi_5(q) = q^4 + q^3 + q^2 + q + 1. The proof is the standard telescoping argument: (q : ZMod p)^5 = 1 gives p | q^5 - 1; the geometric identity (sum_{i<5} q^i) * (q - 1) = q^5 - 1 together with p prime and p not dividing q - 1 (otherwise q would have order 1, not 5) forces p to divide the geometric sum 1 + q + q^2 + q^3 + q^4. This is the Section 16.1 / Section 21 cyclotomic entry point for the distinguished q | t subbranch. Published as an Open research child; no proof is asserted by this submission.
-- source:
--   Sections 16.1 and 21 of artifacts/opn/OPN_LIVE_STATE_2026-09-17.md. Uses the Proved helper OddPerfectNumber.geom_mul_sub_one (node 069159f8-59c6-4023-af9d-5ad6dabcdf1b) for the telescoping identity and the Proved Nat/ZMod bridge OddPerfectNumber.zmod_pow_eq_one_iff (node 890d5806-d6f3-4d4c-8ec3-42d96f9b4165). No BCR, no valuation gap, no IsSquare, no reciprocity.

import Mathlib

namespace OddPerfectNumber

theorem order_five_phi5_dvd (p q : Nat)
    (hp : p.Prime)
    (hq : q.Prime)
    (h5 : orderOf (q : ZMod p) = 5) :
    p ∣ q ^ 4 + q ^ 3 + q ^ 2 + q + 1 := by
  sorry

end OddPerfectNumber
