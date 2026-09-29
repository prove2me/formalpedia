-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q_dvd_d_incoming_core_r_eq_p_after_p_sq_sigma
-- name    : OddPerfectNumber.k_one_q_dvd_d_incoming_core_r_eq_p_after_p_sq_sigma
-- status  : Open
-- author  : @WillR
-- created : 2026-09-12T19:44:12.745212+00:00
-- url     : https://prove2.me/theorems/dff2341b-806e-4f32-a124-ea59a57731a6
-- title:
--   The r=p incoming core after the p-squared valuation step
-- statement:
--   This is the residual r=p incoming-source research core after the elementary valuation consequence p^2 divides sigma(m^2) has been separated. The hypotheses retain the exact canonical q-divides-d interface, the incoming source r=p, and the stronger p-squared divisor-sum fact. No contradiction is asserted by the source; the remaining statement is an explicit research target.
-- source:
--   Acyclic refinement of OddPerfectNumber.k_one_q_dvd_d_incoming_core_r_eq_p. The added hypothesis is supplied by the elementary child OddPerfectNumber.k_one_sigma_sq_dvd_of_incoming_source_eq_p (ID 34e00c5f-c724-4281-8919-c9b816926e1b).

import Mathlib
open Finset

namespace OddPerfectNumber

theorem k_one_q_dvd_d_incoming_core_r_eq_p_after_p_sq_sigma (p m d q r : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hdvd : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hprime : q.Prime) (hqm : q ∣ m) (hqp : q ≠ p) (hqodd : Odd q)
    (hqmem : q ∈ (m ^ 2).primeFactors)
    (hqdvd : p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i)
    (huniq : ∀ y ∈ (m ^ 2).primeFactors,
      p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization y + 1), y ^ i → y = q)
    (hsq : IsSquare (q : ZMod p))
    (hsqP : IsSquare (p : ZMod q))
    (hqd : q ∣ d)
    (hrmem : r ∈ (m ^ 2).primeFactors)
    (hrneq : r ≠ q)
    (hqr : q ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization r + 1), r ^ i)
    (hrp : r = p)
    (hp2sig : p ^ 2 ∣ ∑ x ∈ (m ^ 2).divisors, x) :
    False := by
  sorry

end OddPerfectNumber
