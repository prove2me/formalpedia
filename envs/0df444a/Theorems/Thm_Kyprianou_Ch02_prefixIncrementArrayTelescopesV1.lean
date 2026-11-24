-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prefixIncrementArrayTelescopesV1
-- name    : Kyprianou.Ch02.prefixIncrementArrayTelescopesV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:02:21.9578+00:00
-- url     : https://prove2.me/theorems/e08c28b9-c4e1-4dd3-8e9a-e5a8a6e7823f
-- title:
--   Finite prefix sum recovers the endpoint increment
-- statement:
--   Convert the Fin sum to a natural range, restrict to the prefix k+1, then use the telescoping sum.
-- source:
--   Kyprianou (2006), Exercise 2.8, independence of Jordan variation components.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.prefixIncrementArrayTelescopesV1
    (f : ℕ → ℝ) (n : ℕ) (k : Fin n) :
    (∑ i : Fin n, if i.val ≤ k.val then f (i.val+1)-f i.val else 0) =
      f (k.val+1)-f 0 := by sorry
