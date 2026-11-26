-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46BusySetRestartAssemblyV1
-- name    : Kyprianou.Ch04.exercise46BusySetRestartAssemblyV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:33:32.68588+00:00
-- url     : https://prove2.me/theorems/ff7a517d-ed3f-5685-a3ab-eda841c23525
-- title:
--   Assemble the finite-recovery physical busy-start set
-- statement:
--   Split a busy start according to whether it is before recovery or strictly after it, and translate the latter back.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46BusySetRestartAssemblyV1
    (S T : Set NNReal) (a b : NNReal)
    (ha : a ∈ S) (hab : a ≤ b)
    (hBefore : ∀ t ∈ S, t ≤ b → t = a)
    (hPos : ∀ u ∈ T, 0 < u)
    (hShift : ∀ u : NNReal, 0 < u → (b+u ∈ S ↔ u ∈ T)) :
    S = insert a ((fun u : NNReal => b+u) '' T) := by
  sorry
