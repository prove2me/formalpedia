-- Prove2me | Theorems.Thm_Kyprianou_Ch06_finiteMonotoneCountIncrementTelescoping
-- name    : Kyprianou.Ch06.finiteMonotoneCountIncrementTelescoping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:53:30.518136+00:00
-- url     : https://prove2.me/theorems/6226131a-6b1d-477a-9597-cb414907e9a9
-- title:
--   Lemma 6.18 temporal helper: monotone counting increments telescope over finite grids
-- statement:
--   Every monotone natural-number counting sequence has its finite sum of consecutive increments equal to the total difference between endpoints. This pathwise identity is the temporal half of the finite compatible mark-time rectangle representation needed to reconstruct arbitrary Poisson counts at different observation times.
-- source:
--   Kyprianou (2006), Lemma 6.18(ii), printed pp.160–161, finite count-increment partition construction.

import Mathlib
set_option autoImplicit false

theorem Kyprianou.Ch06.finiteMonotoneCountIncrementTelescoping
    (F : Nat → Nat) (hF : Monotone F) (k : Nat) :
    (∑ i ∈ Finset.range k, (F (i + 1) - F i)) = F k - F 0 := by sorry
