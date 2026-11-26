-- Prove2me | Theorems.Thm_Kyprianou_Ch04_workloadsEventuallyAgree
-- name    : Kyprianou.Ch04.workloadsEventuallyAgree
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:26:11.489774+00:00
-- url     : https://prove2.me/theorems/b572c22d-3d7e-507f-8394-16d92c45b912
-- title:
--   Reflected workloads eventually agree for unbounded supremum
-- statement:
--   Once the running supremum exceeds the initial workload, the two reflected paths agree. The divergence of the supremum implies eventual agreement.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.9 and Theorem 4.10

import Mathlib
open Filter Set MeasureTheory
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.workloadsEventuallyAgree
    (w : ℝ) (S X : NNReal → ℝ)
    (hS : Tendsto S atTop atTop) :
    (fun t => max w (S t) - X t) =ᶠ[atTop] (fun t => S t - X t) := by
  sorry
