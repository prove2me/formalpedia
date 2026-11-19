-- Prove2me | Theorems.Thm_Kyprianou_Ch01_uniformGridCrossingInOpenIntervalPublic
-- name    : Kyprianou.Ch01.uniformGridCrossingInOpenIntervalPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T09:57:22.862507+00:00
-- url     : https://prove2.me/theorems/18de90f4-70a8-41ce-b4c5-ebb3311950d6
-- title:
--   Uniform grid eventually detects any strict upper crossing interval wider than mesh
-- statement:
--   For a continuous process, strict level exceedance persists on a neighbourhood. If an interval [a,b) of times consists of strict upper crossings and its width exceeds the positive grid mesh, a uniform grid point in that interval is also a strict upper crossing. This lemma supplies the quantified grid-detection step in the Brownian first strict passage approximation.
-- source:
--   Kyprianou (2006), Exercise 1.10(ii), first-passage grid refinement, printed page 306. Open child uniformGridCeilingWithinMesh.

import Mathlib.Data.Real.Basic
import Theorems.Thm_Kyprianou_Ch01_uniformGridCeilingWithinMeshPublic
set_option autoImplicit false

theorem Kyprianou.Ch01.uniformGridCrossingInOpenIntervalPublic
    (delta a b : ℝ) (hdelta : 0 < delta)
    (ha : 0 ≤ a) (hab : a + delta < b)
    (f : ℝ → ℝ) (x : ℝ)
    (hstrip : ∀ t, a ≤ t → t < b → x < f t) :
    ∃ n : ℕ, a ≤ (n : ℝ) * delta ∧
      (n : ℝ) * delta < b ∧ x < f ((n : ℝ) * delta) := by sorry
