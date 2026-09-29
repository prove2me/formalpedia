-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_non_source_sigma_not_dvd
-- name    : OddPerfectNumber.k_one_non_source_sigma_not_dvd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-12T19:38:29.278311+00:00
-- url     : https://prove2.me/theorems/71b37b7e-40ff-4918-a9ee-b4a390c0f4fb
-- title:
--   Non-distinguished support primes do not supply p
-- statement:
--   If q is the unique support prime whose local divisor sum is divisible by p, then every other support prime r has a local divisor sum not divisible by p. This is the direct contraposition of the canonical uniqueness hypothesis.
-- source:
--   Elementary contraposition of the exact huniq interface in OddPerfectNumber.k_one_endgame_q_dvd_d_incoming_core; no additional number-theoretic assumption is used.

import Mathlib
open Finset

namespace OddPerfectNumber

theorem k_one_non_source_sigma_not_dvd (p m q r : Nat)
    (huniq : ∀ y ∈ (m ^ 2).primeFactors,
      p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization y + 1), y ^ i → y = q)
    (hrmem : r ∈ (m ^ 2).primeFactors) (hrneq : r ≠ q) :
    ¬ p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization r + 1), r ^ i := by
  sorry

end OddPerfectNumber
