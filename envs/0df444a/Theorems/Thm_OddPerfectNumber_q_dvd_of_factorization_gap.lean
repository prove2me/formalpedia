-- Prove2me | Theorems.Thm_OddPerfectNumber_q_dvd_of_factorization_gap
-- name    : OddPerfectNumber.q_dvd_of_factorization_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-12T17:50:40.537155+00:00
-- url     : https://prove2.me/theorems/3eb35d7c-57d6-466b-b721-64c84f20ce08
-- title:
--   A strict q-adic factorization gap forces q into the cofactor
-- statement:
--   Let q be prime and let m² = t d with all displayed numbers nonzero. If the q-adic exponent of m² is strictly larger than the q-adic exponent of t, then q divides d. This is the elementary factorization bookkeeping needed to turn a Brent-style lower bound A ≥ 3r into q ∣ d in the k = 1 q-divides-t branch.
-- source:
--   Elementary consequence of Nat.factorization_mul and the definition of prime support; introduced as a reusable bookkeeping lemma for the Odd Perfect Number Conjecture q-divides-t reduction.

import Mathlib

namespace OddPerfectNumber

theorem q_dvd_of_factorization_gap (q t d m A r : Nat)
    (hq : q.Prime) (hm2 : m ^ 2 ≠ 0) (ht0 : t ≠ 0) (hd0 : d ≠ 0)
    (hdvd : m ^ 2 = t * d)
    (hA : (m ^ 2).factorization q = A)
    (hr : t.factorization q = r)
    (hstrict : r < A) :
    q ∣ d := by
  sorry

end OddPerfectNumber
