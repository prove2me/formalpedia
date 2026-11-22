-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_tupleProduct_insertNth
-- name    : LongGapsBetweenPrimes.tupleProduct_insertNth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:44:18.435192+00:00
-- url     : https://prove2.me/theorems/3efea9bd-af59-43de-be32-eadbc2a55c3d
-- title:
--   Long Gaps Between Primes: tuple Product insert Nth
-- statement:
--   Inserting a divisor multiplies the tuple product by that divisor.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2702-L2706
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2702-L2706

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.tupleProduct_insertNth {P k : ℕ} (i : Fin (k + 1)) (d : DivisorIndex P)
    (r : DivisorTuple P k) : tupleProduct (i.insertNth d r) = d.val * tupleProduct r := by sorry
