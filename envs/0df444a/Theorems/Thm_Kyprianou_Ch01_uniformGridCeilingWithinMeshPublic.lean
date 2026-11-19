-- Prove2me | Theorems.Thm_Kyprianou_Ch01_uniformGridCeilingWithinMeshPublic
-- name    : Kyprianou.Ch01.uniformGridCeilingWithinMeshPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T09:41:45.359013+00:00
-- url     : https://prove2.me/theorems/1868f830-beba-40c4-9f80-a00876529712
-- title:
--   Uniform positive-mesh rounding finds a grid point less than one step above any time
-- statement:
--   For a nonnegative real time t and a strictly positive uniform grid spacing delta, there exists an integer grid index n with t ≤ n delta < t+delta. This deterministic approximation is a necessary ingredient for proving continuous first strict crossing is approached by discrete grid crossing times as the mesh tends to zero.
-- source:
--   Kyprianou (2006), Exercise 1.10(ii), passage-grid convergence step, printed page 306.

import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
set_option autoImplicit false

theorem Kyprianou.Ch01.uniformGridCeilingWithinMeshPublic
    (delta t : ℝ) (hdelta : 0 < delta) (ht : 0 ≤ t) :
    ∃ n : ℕ, t ≤ (n : ℝ) * delta ∧
      (n : ℝ) * delta < t + delta := by sorry
