-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_localKernel_symm
-- name    : LongGapsBetweenPrimes.localKernel_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:35.562729+00:00
-- url     : https://prove2.me/theorems/f4ec93b3-a495-41e9-b62c-3702cc6e1605
-- title:
--   Long Gaps Between Primes: local Kernel symm
-- statement:
--   The local Gram kernel is symmetric.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L585-L587
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L585-L587

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.localKernel_symm (p : ℕ) {k : ℕ} (i j : Option (Fin k)) :
    localKernel p i j = localKernel p j i := by sorry
