-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_average_localBasis_mul
-- name    : LongGapsBetweenPrimes.average_localBasis_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:23.227312+00:00
-- url     : https://prove2.me/theorems/bf8718c4-e93e-4e73-bf81-373b1a85e160
-- title:
--   Long Gaps Between Primes: average local Basis mul
-- statement:
--   The local Gram matrix, with the nonconstant factors normalized to variance one.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L551-L576
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L551-L576

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.average_localBasis_mul {p k : ℕ} (hp : 1 < p) (root : Fin k → Fin p)
    (hroot : Function.Injective root) (i j : Option (Fin k)) :
    Finset.expect Finset.univ (fun t => localBasis root i t * localBasis root j t) =
      localKernel p i j := by sorry
