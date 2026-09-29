-- Prove2me | Theorems.Thm_OddPerfectNumber_p_dvd_d_of_incoming_source_eq_p
-- name    : OddPerfectNumber.p_dvd_d_of_incoming_source_eq_p
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-12T17:58:08.093303+00:00
-- url     : https://prove2.me/theorems/ad405d5f-b8dd-4881-8e0a-1ac2bb070815
-- title:
--   An incoming source equal to p forces p into d
-- statement:
--   In the canonical k=1 product equation, if a support prime r of m² is the Euler prime p itself, then p divides the Dris cofactor d. The proof is elementary: p divides m², p does not divide the odd quotient (p+1)/2, and primality applied to m² = ((p+1)/2)d forces p into d. This is a reusable structural fact for the r=p incoming-source branch.
-- source:
--   Elementary consequence of Euler-prime parity, Nat.mem_primeFactors, and prime divisibility of a product; introduced for the Odd Perfect Number Conjecture incoming-source analysis.

import Mathlib

namespace OddPerfectNumber

theorem p_dvd_d_of_incoming_source_eq_p (p m d r : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hdvd : m ^ 2 = ((p + 1) / 2) * d)
    (hrmem : r ∈ (m ^ 2).primeFactors)
    (hrp : r = p) :
    p ∣ d := by
  sorry

end OddPerfectNumber
