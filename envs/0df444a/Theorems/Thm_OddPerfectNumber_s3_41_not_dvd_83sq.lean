-- Prove2me | Theorems.Thm_OddPerfectNumber_s3_41_not_dvd_83sq
-- name    : OddPerfectNumber.s3_41_not_dvd_83sq
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-19T21:12:48.266987+00:00
-- url     : https://prove2.me/theorems/82240cb9-1f4e-4e81-a6c4-8c0dc2710b69
-- title:
--   83^2 does not divide the base-3 geometric sum of index 41
-- statement:
--   Finite certificate: 83^2 does not divide 1 + 3 + ... + 3^40 (the residue is 1328).
-- source:
--   37 <= q3 <= 61 four-support block, finite q4^2 nondivisibility certificate for q4 = 83, t = 41.

import Mathlib

namespace OddPerfectNumber

theorem s3_41_not_dvd_83sq :
    ¬ 83 ^ 2 ∣ ∑ i ∈ Finset.range 41, 3 ^ i := by
  sorry

end OddPerfectNumber
