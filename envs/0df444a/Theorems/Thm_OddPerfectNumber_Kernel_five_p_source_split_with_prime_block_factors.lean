-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_p_source_split_with_prime_block_factors
-- name    : OddPerfectNumber.Kernel.five_p_source_split_with_prime_block_factors
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T01:17:22.613323+00:00
-- url     : https://prove2.me/theorems/4effc146-a20b-4958-91fb-ae9e7cb6e650
-- title:
--   Source localisation with primality of the two block factors
-- statement:
--   Let m equal 3 times u times a times b times d1 times q times r, with q and r both prime, and let t be a prime dividing m different from 3, q and r. Then t equals q, or t equals r, or t divides the square part u times a times b times d1. This is the corrected form of five_odd_p_source_is_middle_or_square_part, which was disproved because it omitted the primality of q and r, so that from t dividing q one could conclude only t at most q.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_p_source_split_with_prime_block_factors {m u a b d1 q r t : Nat}
    (hshape : m = 3 * u * a * b * d1 * q * r) (hq : q.Prime) (hr : r.Prime)
    (ht : t.Prime) (htd : Dvd.dvd t m) (ht3 : t != 3) (htq : t != q) (htr : t != r) :
    t = q ∨ Dvd.dvd t (u * a * b * d1) ∨ t = r := by
  sorry

end OddPerfectNumber.Kernel
