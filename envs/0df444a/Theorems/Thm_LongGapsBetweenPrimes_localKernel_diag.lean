-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_localKernel_diag
-- name    : LongGapsBetweenPrimes.localKernel_diag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:45.422597+00:00
-- url     : https://prove2.me/theorems/a3170597-fd8b-4ddc-84ec-94c8437e8602
-- title:
--   Long Gaps Between Primes: local Kernel diag
-- statement:
--   The local Gram kernel has diagonal entries equal to one.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L590-L591
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L590-L591

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.localKernel_diag (p : ℕ) {k : ℕ} (i : Option (Fin k)) :
    localKernel p i i = 1 := by sorry
