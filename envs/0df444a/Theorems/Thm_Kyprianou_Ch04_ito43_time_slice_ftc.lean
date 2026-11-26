-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_time_slice_ftc
-- name    : Kyprianou.Ch04.ito43_time_slice_ftc
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:16:13.322414+00:00
-- url     : https://prove2.me/theorems/6ad2dff5-93b6-598e-aef7-99a16240c6ac
-- title:
--   Fixed-position time increment equals integral of continuous within derivative
-- statement:
--   Fixed-position time increment equals integral of continuous within derivative.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3, supporting lemma.

import Mathlib
open MeasureTheory Set Filter
open scoped Topology
set_option autoImplicit false

/-- Time increments at a fixed position are integrals of the continuous within-half-plane derivative. -/

theorem Kyprianou.Ch04.ito43_time_slice_ftc (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Ici (0 : ℝ) ×ˢ (univ : Set ℝ)))
    (a b x : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ s in Icc a b, fderivWithin ℝ f
      (Ici (0 : ℝ) ×ˢ (univ : Set ℝ)) (s,x) (1,0)) =
      f (b,x) - f (a,x) := by sorry
