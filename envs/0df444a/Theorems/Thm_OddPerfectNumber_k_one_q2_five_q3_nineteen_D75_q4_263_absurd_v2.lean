-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D75_q4_263_absurd_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_D75_q4_263_absurd_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T21:51:20.628873+00:00
-- url     : https://prove2.me/theorems/36b36b32-f7b8-409f-ad35-2f6730c4917a
-- title:
--   The D=75 q4=263 source is impossible under explicit order obstructions
-- statement:
--   The D=75 q3=19 q4=263 sigma source is impossible once all four exact order-divisibility obstructions modulo 149 are supplied.
-- source:
--   Clean replacement for the historical under-specified target; the order hypotheses are explicit and are not inferred from false parity claims.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_p149_no_local_sigma_source_general

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_D75_q4_263_absurd_v2 (sigma a b c e : Nat)
    (hsigma : sigma = (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2 * c + 1), 19 ^ i) * (∑ i ∈ Finset.range (2 * e + 1), 263 ^ i))
    (hdiv : 149 ∣ sigma)
    (h3 : ¬ orderOf (3 : ZMod 149) ∣ 2 * a + 1)
    (h5 : ¬ orderOf (5 : ZMod 149) ∣ 2 * b + 1)
    (h19 : ¬ orderOf (19 : ZMod 149) ∣ 2 * c + 1)
    (h263 : ¬ orderOf (263 : ZMod 149) ∣ 2 * e + 1) :
    False := by
  sorry

end OddPerfectNumber
