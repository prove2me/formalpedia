-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q_dvd_d_of_q_dvd_t
-- name    : OddPerfectNumber.k_one_q_dvd_d_of_q_dvd_t
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-12T16:52:57.795174+00:00
-- url     : https://prove2.me/theorems/e3e2a26a-efd5-4b2d-b64b-e5804d2f977d
-- title:
--   The q-divides-t branch reduces to q dividing the Dris cofactor
-- statement:
--   Under the exact canonical k=1 q-divides-t hypotheses, the distinguished prime q also divides the Dris cofactor d. The intended source-backed route is Brent--Cohen--te Riele Lemma 1: with A equal to the q-adic exponent of m^2 and r equal to the q-adic exponent of (p+1)/2, the conditions p dividing sigma(q^A) and q^r exactly dividing p+1 give A at least 3r; taking q-adic valuations in m^2=((p+1)/2)d then gives v_q(d) at least 2r. This theorem is published as an Open research child until that valuation lemma is formally proved.
-- source:
--   Acyclic reduction target for the canonical q-divides-t leaf. The mathematical input is R. P. Brent, G. L. Cohen and H. J. J. te Riele, Improved Techniques for Lower Bounds for Odd Perfect Numbers, Lemma 1 (sharp bound A >= 3r). The exact valuation interface must be proved before this child is treated as closed.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q_dvd_d_of_q_dvd_t (p m d q : Nat)
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
    (hqt : q ∣ (p + 1) / 2) :
    q ∣ d := by
  sorry

end OddPerfectNumber
