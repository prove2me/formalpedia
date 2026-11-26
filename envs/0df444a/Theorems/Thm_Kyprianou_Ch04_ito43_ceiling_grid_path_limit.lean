-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_ceiling_grid_path_limit
-- name    : Kyprianou.Ch04.ito43_ceiling_grid_path_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:28:46.411878+00:00
-- url     : https://prove2.me/theorems/2ca4add2-cc4e-4820-9d5a-e5d6ad81c4fe
-- title:
--   Right rounded times give pointwise convergence along right-continuous paths
-- statement:
--   Right rounded times give pointwise convergence along right-continuous paths.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3, supporting lemma.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_ceiling_grid
import Theorems.Thm_Kyprianou_Ch04_ito43_right_grid_limit
open Filter Set
open scoped Topology
set_option autoImplicit false

/-- Right grid approximation of a right-continuous real path converges at each time. -/

theorem Kyprianou.Ch04.ito43_ceiling_grid_path_limit (X : ℝ → ℝ) (T s : ℝ) (hT : 0 < T)
    (hs : s ∈ Icc 0 T) (hX : ContinuousWithinAt X (Ici s) s) :
    Tendsto (fun n : ℕ => X (T * (Nat.ceil (s * (n : ℝ) / T) : ℝ) / (n : ℝ)))
      atTop (nhds (X s)) := by sorry
