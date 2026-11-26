-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_stopped_grid_cutoff_cell
-- name    : Kyprianou.Ch04.ito43_stopped_grid_cutoff_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:33:43.483322+00:00
-- url     : https://prove2.me/theorems/5f216b79-0b25-41f6-b4bb-3dc1bf981d6a
-- title:
--   Stopped-cell Taylor remainder uses clipped spatial derivative
-- statement:
--   Stopped-cell Taylor remainder uses clipped spatial derivative.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open Set
open scoped NNReal
set_option autoImplicit false

/-- On a stopped cell, derivatives at the unclipped time give the same Taylor excess
as derivatives at the clipped time: after the stopping horizon the increment is zero. -/

theorem Kyprianou.Ch04.ito43_stopped_grid_cutoff_cell (X : NNReal → ℝ) (f : ℝ × ℝ → ℝ)
    (u : ℕ → NNReal) (hu : Monotone u) (t : NNReal) (k : ℕ) :
    let v : ℕ → NNReal := fun j => min t (u j)
    let d := X (v (k+1))-X (v k)
    (f ((v k : ℝ),X (v (k+1)))-f ((v k : ℝ),X (v k)) -
      deriv (fun x : ℝ => f ((u k : ℝ),x)) (X (u k))*d -
      iteratedDeriv 2 (fun x : ℝ => f ((u k : ℝ),x)) (X (u k))*d^2/2) =
    (f ((v k : ℝ),X (v (k+1)))-f ((v k : ℝ),X (v k)) -
      deriv (fun x : ℝ => f ((v k : ℝ),x)) (X (v k))*d -
      iteratedDeriv 2 (fun x : ℝ => f ((v k : ℝ),x)) (X (v k))*d^2/2) := by sorry
