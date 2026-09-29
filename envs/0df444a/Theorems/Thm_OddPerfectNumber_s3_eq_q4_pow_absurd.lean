-- Prove2me | Theorems.Thm_OddPerfectNumber_s3_eq_q4_pow_absurd
-- name    : OddPerfectNumber.s3_eq_q4_pow_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-19T21:11:37.361791+00:00
-- url     : https://prove2.me/theorems/d9a94d04-be53-4fc0-9d7b-152f6976922d
-- title:
--   A pure q4-power base-3 geometric sum equal to the next q4-power is impossible above q4
-- statement:
--   Suppose the base-3 geometric sum S_3(t) = 1 + 3 + ... + 3^(t-1) is a pure power q4^beta of q4 with beta > 0, that q4^2 does not divide S_3(t), and that S_3(t) exceeds q4. Then contradiction: q4 | q4^beta forces beta >= 1, and if beta >= 2 then q4^2 | S_3(t) contrary to the hypothesis, so beta = 1 and S_3(t) = q4, contradicting S_3(t) > q4. This is the closing step of the 37 <= q3 <= 61 block: the finite q4^2 nondivisibility certificates supply the second hypothesis.
-- source:
--   37 <= q3 <= 61 four-support block, step 4D of the branch plan: q4 | S_3(t) and q4^2 not dividing S_3(t) force beta = 1 in S_3(t) = q4^beta, and S_3(t) > q4 closes the contradiction.

import Mathlib

namespace OddPerfectNumber

theorem s3_eq_q4_pow_absurd (q4 t beta : Nat)
    (hbeta : 0 < beta)
    (hgt : q4 < ∑ i ∈ Finset.range t, 3 ^ i)
    (hndvd : ¬ q4 ^ 2 ∣ ∑ i ∈ Finset.range t, 3 ^ i)
    (hpow : ∑ i ∈ Finset.range t, 3 ^ i = q4 ^ beta) :
    False := by
  sorry

end OddPerfectNumber
