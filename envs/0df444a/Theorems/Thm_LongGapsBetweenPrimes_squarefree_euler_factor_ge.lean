-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_squarefree_euler_factor_ge
-- name    : LongGapsBetweenPrimes.squarefree_euler_factor_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:05.790681+00:00
-- url     : https://prove2.me/theorems/5e2770b2-d7fc-4734-bbda-1510eb7b4579
-- title:
--   Long Gaps Between Primes: squarefree euler factor ge
-- statement:
--   A squarefree Euler factor dominates the corresponding shifted geometric factor.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1215-L1225
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1215-L1225

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.squarefree_euler_factor_ge {p t : ℝ} (hp : 1 < p) (ht : 0 < t) :
    (1 - p ^ (-(1 + t)))⁻¹ ≤ 1 + p ^ (-t) / (p - 1) := by sorry
