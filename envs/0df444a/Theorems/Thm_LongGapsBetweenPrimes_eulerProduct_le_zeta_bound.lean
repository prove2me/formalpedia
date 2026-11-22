-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_eulerProduct_le_zeta_bound
-- name    : LongGapsBetweenPrimes.eulerProduct_le_zeta_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:41.745052+00:00
-- url     : https://prove2.me/theorems/e38bdbd1-0da3-4d40-99f4-34d753280851
-- title:
--   Long Gaps Between Primes: euler Product le zeta bound
-- statement:
--   For `σ > 1`, the finite Euler product is at most `1 + 1 / (σ - 1)`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1025-L1042
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1025-L1042

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.eulerProduct_le_zeta_bound {σ : ℝ} (hσ : 1 < σ) (N : ℕ) :
    eulerProduct N σ ≤ 1 + 1 / (σ - 1) := by sorry
