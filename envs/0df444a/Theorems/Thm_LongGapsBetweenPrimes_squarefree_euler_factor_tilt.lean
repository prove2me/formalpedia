-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_squarefree_euler_factor_tilt
-- name    : LongGapsBetweenPrimes.squarefree_euler_factor_tilt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:48.726282+00:00
-- url     : https://prove2.me/theorems/706639f4-1934-4531-b8a9-54fbf292bd69
-- title:
--   Long Gaps Between Primes: squarefree euler factor tilt
-- statement:
--   An exponential bound for tilting a squarefree Euler factor.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1489-L1509
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1489-L1509

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.squarefree_euler_factor_tilt {p γ E : ℝ} (hp : 1 < p)
    (hγ : 0 ≤ γ) (hpE : p ^ γ ≤ E) :
    1 + p ^ γ / (p - 1) ≤
      (1 + 1 / (p - 1)) * Real.exp (E * γ * Real.log p / p) := by sorry
