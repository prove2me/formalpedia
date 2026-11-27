-- Prove2me | Theorems.Thm_Kyprianou_Ch04_clippedGridWindowCellIntegralV1
-- name    : Kyprianou.Ch04.clippedGridWindowCellIntegralV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:37:37.74068+00:00
-- url     : https://prove2.me/theorems/34e4c125-2a4b-4027-9e45-cf9f2aa8be5c
-- title:
--   clippedGridWindowCellIntegralV1
-- statement:
--   Physical grid kernel estimate.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5

import Mathlib
open MeasureTheory Set
open scoped NNReal
set_option autoImplicit false

/-- A right-closed grid cell restricted to the observation window equals the
difference of two nested clipped windows, with no time-zero assumption. -/

theorem Kyprianou.Ch04.clippedGridWindowCellIntegralV1 (R : Measure (ℝ × ℝ)) (Q : ℝ × ℝ → ℝ)
    (T t a b : NNReal) (ht : t ≤ T) (hab : a ≤ b)
    (hQ : IntegrableOn Q (Icc (0 : ℝ) (T : ℝ) ×ˢ (univ : Set ℝ)) R)
    (c : ℝ) :
    (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ),
      (Ioc a b).indicator (fun _ => c) z.1.toNNReal * Q z ∂ R) =
      c * ((∫ z in Icc (0 : ℝ) ((min t b : NNReal) : ℝ) ×ˢ (univ : Set ℝ), Q z ∂ R) -
        ∫ z in Icc (0 : ℝ) ((min t a : NNReal) : ℝ) ×ˢ (univ : Set ℝ), Q z ∂ R) := by
  sorry
