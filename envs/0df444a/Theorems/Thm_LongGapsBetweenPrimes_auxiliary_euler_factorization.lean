-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_auxiliary_euler_factorization
-- name    : LongGapsBetweenPrimes.auxiliary_euler_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:31:35.818694+00:00
-- url     : https://prove2.me/theorems/ea787af8-5746-4821-98cb-b9c94234a601
-- title:
--   Long Gaps Between Primes: auxiliary euler factorization
-- statement:
--   Split the Euler product at the lower cutoff `Z`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1210-L1212
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1210-L1212

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.auxiliary_euler_factorization {Z Y : ℕ} (hZY : Z ≤ Y) (σ : ℝ) :
    (∏ p ∈ auxiliaryPrimes Z Y, (1 - (p : ℝ) ^ (-σ))⁻¹) * eulerProduct Z σ =
      eulerProduct Y σ := by sorry
