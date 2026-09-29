-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_absurd_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_absurd_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T04:18:14.95935+00:00
-- url     : https://prove2.me/theorems/d7445d07-34fa-41e9-804b-3d0b83c09656
-- title:
--   Canonical q3=23 large-D contradiction
-- statement:
--   The canonical q3=23 large-D envelope leaves five exact tuples; q4=53 and q4=59 contradict the accepted residual-5 source obstructions, while q4=61 forces an external 131 source and contradicts finite-support sigma restriction.
-- source:
--   Pure composition of the accepted q3=23 large-D candidate reduction and three exact source contradictions; no candidate tuple is assumed as an incoming premise.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_support_cut_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_source_bridge_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_61_source_bridge_v1

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_large_D_absurd_v2
    (m a b c e D p q4 sigma d : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hDlow : 111 ≤ D) (hDhigh : D ≤ 685)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 47 < q4) (hq4le : q4 ≤ 61)
    (hq4dvd : q4 ∣ D)
    (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4)
    (hb : 1 ≤ b) (hm0 : m ≠ 0)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d) (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 23 ∨ x = q4)
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x) :
    False := by
  sorry

end OddPerfectNumber
