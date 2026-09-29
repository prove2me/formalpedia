-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q_dvd_d_incoming_core_r_ne_p
-- name    : OddPerfectNumber.k_one_q_dvd_d_incoming_core_r_ne_p
-- status  : Open
-- author  : @WillR
-- created : 2026-09-12T16:59:09.480902+00:00
-- url     : https://prove2.me/theorems/b45e31fd-1871-4d19-a57c-c5f31ad02334
-- title:
--   Incoming q-chain residual when the source is not the Euler prime
-- statement:
--   The r≠p branch of the q-divides-d incoming-edge residual. The source prime feeding q is a non-Euler support prime, so the remaining problem is the genuinely global factor-chain case, where uniqueness of the p-source must be combined with order, valuation, new-prime, or abundance information. This is an Open research core, not a claimed contradiction.
-- source:
--   Acyclic case split of the published incoming-edge residual for the canonical q-divides-d endgame. The branch is the r != p case requested by the valuation-flow programme; finite support alone is not treated as termination.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q_dvd_d_incoming_core_r_ne_p (p m d q r : Nat)
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
    (hrp : r ≠ p) :
    False := by
  sorry

end OddPerfectNumber
