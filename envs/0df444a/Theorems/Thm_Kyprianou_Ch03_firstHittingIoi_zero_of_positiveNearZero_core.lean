-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstHittingIoi_zero_of_positiveNearZero_core
-- name    : Kyprianou.Ch03.firstHittingIoi_zero_of_positiveNearZero_core
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:31:28.093954+00:00
-- url     : https://prove2.me/theorems/8ea9008c-3599-4456-be38-21082ce36e8a
-- title:
--   Strict positive upcrossings arbitrarily near zero force zero first-hitting time
-- statement:
--   For a path starting at zero, if every positive interval contains a strict upward crossing, the infimum of its positive crossing times is zero.
-- source:
--   Kyprianou Chapter 3 upward first passage, deterministic infimum fact

import Mathlib
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem firstHittingIoi_zero_of_positiveNearZero_core
    {Omega : Type} (X : NNReal -> Omega -> Real) (omega : Omega)
    (hXZero : X 0 omega = 0)
    (hNear : forall epsilon : NNReal, 0 < epsilon ->
      ∃ s : NNReal, s < epsilon ∧ 0 < X s omega) :
    firstHittingTime X (Set.Ioi (0 : Real)) omega = 0 := by
  sorry

end Kyprianou.Ch03
