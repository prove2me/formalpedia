-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_sum_abs_localKernel
-- name    : LongGapsBetweenPrimes.sum_abs_localKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:46.173805+00:00
-- url     : https://prove2.me/theorems/f879a351-ba2d-4dad-931c-2f3b290a6937
-- title:
--   Long Gaps Between Primes: sum abs local Kernel
-- statement:
--   Summing the absolute local kernel entries gives `localRow`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L594-L603
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L594-L603

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.sum_abs_localKernel {p k : ℕ} (hp : 1 < p) (i : Option (Fin k)) :
    (∑ j, |localKernel p i j|) = localRow p k i := by sorry
