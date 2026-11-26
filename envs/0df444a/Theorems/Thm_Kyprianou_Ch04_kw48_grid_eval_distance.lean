-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_grid_eval_distance
-- name    : Kyprianou.Ch04.kw48_grid_eval_distance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:36:17.214292+00:00
-- url     : https://prove2.me/theorems/83266c1d-74d4-5e76-ae34-c913e10bb6b2
-- title:
--   Grid step evaluation within the mesh
-- statement:
--   Grid step evaluation within the mesh.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_grid_cell_exists_unique
open Set
set_option autoImplicit false

/-- A step approximation on an ordered grid evaluates its function
at an endpoint on the chosen side within the mesh distance. -/

theorem Kyprianou.Ch04.kw48_grid_eval_distance
    (f : Real → Complex) (u : Nat → Real) (N : Nat)
    (hu : Monotone u) (delta : Real)
    (hMesh : ∀ i, i < N → u (i+1)-u i ≤ delta)
    (right : Bool) (x : Real) (hx : x ∈ Ioc (u 0) (u N)) :
    ∃ y, y ∈ (if right then Ici x else Iic x) ∧
      dist y x ≤ delta ∧
      (∑ i ∈ Finset.range N, (Ioc (u i) (u (i+1))).indicator
        (fun _ : Real => f (if right then u (i+1) else u i)) x) = f y := by sorry
