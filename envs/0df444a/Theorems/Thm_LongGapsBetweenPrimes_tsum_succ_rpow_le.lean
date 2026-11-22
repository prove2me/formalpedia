-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_tsum_succ_rpow_le
-- name    : LongGapsBetweenPrimes.tsum_succ_rpow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:35.657796+00:00
-- url     : https://prove2.me/theorems/ed39b4f6-9fb5-42b5-85e5-ec1d7165d7a2
-- title:
--   Long Gaps Between Primes: tsum succ rpow le
-- statement:
--   The elementary zeta-function bound obtained by integrating t^(-σ).
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1005-L1022
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1005-L1022

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.tsum_succ_rpow_le {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ)) ≤ 1 + 1 / (σ - 1) := by sorry
