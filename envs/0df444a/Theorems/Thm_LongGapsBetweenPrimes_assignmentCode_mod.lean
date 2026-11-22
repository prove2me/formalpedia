-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_assignmentCode_mod
-- name    : LongGapsBetweenPrimes.assignmentCode_mod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:43:21.435695+00:00
-- url     : https://prove2.me/theorems/410d8eeb-b098-443d-aeac-b1c1f933f37e
-- title:
--   Long Gaps Between Primes: assignment Code mod
-- statement:
--   The assignment code has the prescribed residue at each assigned prime.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2460-L2463
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2460-L2463

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.assignmentCode_mod {P k : ℕ} (root : (p : PrimeIndex P) → Fin k → Fin p.val)
    (σ : PrimeIndex P → Option (Fin k)) (p : PrimeIndex P) (hp : (σ p).isSome) :
    assignmentCode root σ % p.val = (assignedRoot root σ p).val := by sorry
