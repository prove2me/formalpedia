-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_average_residueFactor_sq
-- name    : LongGapsBetweenPrimes.average_residueFactor_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:20.457489+00:00
-- url     : https://prove2.me/theorems/a43b0960-fada-4e2d-941e-27a2915e8319
-- title:
--   Long Gaps Between Primes: average residue Factor sq
-- statement:
--   The residue factor has second moment `1 / (p - 1)`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L522-L526
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L522-L526

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.average_residueFactor_sq {p : ℕ} (hp : 1 < p) (a : Fin p) :
    Finset.expect Finset.univ (fun t => residueFactor a t ^ 2) = 1 / ((p : ℝ) - 1) := by sorry
