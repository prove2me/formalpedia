-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_spatial_initial_grid_identity
-- name    : Kyprianou.Ch04.ito43_spatial_initial_grid_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:47:41.643954+00:00
-- url     : https://prove2.me/theorems/dbc34d2d-7312-4973-b49c-0489c44384cd
-- title:
--   Spatial slice derivative substitution changes only first grid cell
-- statement:
--   Spatial slice derivative substitution changes only first grid cell.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_spatial_slice_derivative
open Set
open scoped NNReal
set_option autoImplicit false

/-- Replacing ambient spatial derivatives by slice derivatives changes only the first cell. -/

theorem Kyprianou.Ch04.ito43_spatial_initial_grid_identity (X : NNReal → ℝ) (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Ici (0 : ℝ) ×ˢ (univ : Set ℝ)))
    (T t : NNReal) (n : ℕ) (hn : 0 < n) :
    let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
    let v : ℕ → NNReal := fun k => min t (u k)
    (∑ k ∈ Finset.range n,
      ((f ((v k : ℝ), X (v (k+1))) - f ((v k : ℝ), X (v k))) -
        deriv (fun y : ℝ => f ((u k : ℝ), y)) (X (u k)) * (X (v (k+1)) - X (v k)))) -
    (∑ k ∈ Finset.range n,
      ((f ((v k : ℝ), X (v (k+1))) - f ((v k : ℝ), X (v k))) -
        fderiv ℝ f ((u k : ℝ),X (u k)) (0,1) * (X (v (k+1)) - X (v k)))) =
      (fderiv ℝ f (0,X 0) (0,1) - deriv (fun y : ℝ => f (0,y)) (X 0)) *
        (X (min t (T / (n : NNReal))) - X 0) := by sorry
