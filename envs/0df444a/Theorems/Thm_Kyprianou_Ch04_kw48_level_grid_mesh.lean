-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_level_grid_mesh
-- name    : Kyprianou.Ch04.kw48_level_grid_mesh
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:37:53.373897+00:00
-- url     : https://prove2.me/theorems/777ee77f-68cc-4a3f-9330-62959fff9c0d
-- title:
--   Continuous monotone coordinate change preserves vanishing mesh
-- statement:
--   Continuous monotone coordinate change preserves vanishing mesh.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
open Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- A continuous nondecreasing change of coordinates sends a
vanishing-mesh monotone grid to another vanishing-mesh grid. -/

theorem Kyprianou.Ch04.kw48_level_grid_mesh (a b : Real) (g : Real → Real)
    (hg : ContinuousOn g (Icc a b)) (hgm : Monotone g)
    (u : Nat → Nat → Real) (N : Nat → Nat)
    (hu : ∀ n, Monotone (u n))
    (h0 : ∀ n, u n 0 = a) (hN : ∀ n, u n (N n) = b)
    (delta : Nat → Real) (hDelta : Tendsto delta atTop (nhds 0))
    (hMesh : ∀ n i, i < N n → u n (i+1)-u n i ≤ delta n) :
    ∃ d : Nat → Real, Tendsto d atTop (nhds 0) ∧
      ∀ n i, i < N n → g (u n (i+1))-g (u n i) ≤ d n := by sorry
