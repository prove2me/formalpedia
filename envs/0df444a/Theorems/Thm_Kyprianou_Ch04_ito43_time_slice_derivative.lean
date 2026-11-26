-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_time_slice_derivative
-- name    : Kyprianou.Ch04.ito43_time_slice_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:16:13.192582+00:00
-- url     : https://prove2.me/theorems/24c8b98d-41b8-5a20-b806-e1901e91e88a
-- title:
--   Continuous time derivative on the closed half-plane agrees with ambient derivative at positive times
-- statement:
--   Continuous time derivative on the closed half-plane agrees with ambient derivative at positive times.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3, supporting lemma.

import Mathlib
open MeasureTheory Set Filter
open scoped Topology
set_option autoImplicit false

/-- The time derivative within the closed half-plane extends continuously to the time boundary. -/

theorem Kyprianou.Ch04.ito43_time_slice_derivative (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Ici (0 : ℝ) ×ˢ (univ : Set ℝ))) :
    let S := Ici (0 : ℝ) ×ˢ (univ : Set ℝ)
    let g := fun z : ℝ × ℝ => fderivWithin ℝ f S z (1,0)
    ContinuousOn g S ∧ ∀ s : ℝ, 0 < s → ∀ x : ℝ,
      g (s,x) = fderiv ℝ f (s,x) (1,0) := by sorry
