-- Prove2me | Theorems.Thm_OddPerfectNumber_brent_cohen_te_riele_sigma_exp_bound
-- name    : OddPerfectNumber.brent_cohen_te_riele_sigma_exp_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-12T16:52:31.697134+00:00
-- url     : https://prove2.me/theorems/a49802f6-c22d-49ff-be55-c93752c05608
-- title:
--   Brent-Cohen-te Riele valuation bound for a prime-power sigma divisor
-- statement:
--   For distinct odd primes p and q, if q^r exactly divides p+1 with r positive and p divides the local geometric sum sigma(q^A)=1+q+...+q^A, then A is at least 3r. This is the exact valuation/order bound attributed to Brent, Cohen and te Riele, Improved Techniques for Lower Bounds for Odd Perfect Numbers, Lemma 1. It is published here as an Open research child only; no proof is asserted by this submission.
-- source:
--   R. P. Brent, G. L. Cohen and H. J. J. te Riele, Improved Techniques for Lower Bounds for Odd Perfect Numbers, CWI manuscript (1991), Lemma 1. The statement uses exact divisibility q^r || p+1 and p | sigma(q^A), and records the sharp bound A >= 3r. The exact source must be checked before relying on any stronger or differently oriented formulation.

import Mathlib

namespace OddPerfectNumber

theorem brent_cohen_te_riele_sigma_exp_bound (p q A r : Nat)
    (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hpq : p ≠ q) (hr : 1 ≤ r)
    (hqr : q ^ r ∣ p + 1)
    (hqr_exact : ¬ q ^ (r + 1) ∣ p + 1)
    (hsigma : p ∣ ∑ i ∈ Finset.range (A + 1), q ^ i) :
    3 * r ≤ A := by
  sorry

end OddPerfectNumber
