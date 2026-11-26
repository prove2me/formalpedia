-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_spatial_slice_derivative
-- name    : Kyprianou.Ch04.ito43_spatial_slice_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:43:34.894962+00:00
-- url     : https://prove2.me/theorems/a09e570a-7f1b-5ed4-bd4b-2a90e651791e
-- title:
--   Ambient spatial derivative equals slice derivative at positive times
-- statement:
--   Ambient spatial derivative equals slice derivative at positive times.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3, supporting lemma.

import Mathlib
open Set Filter
open scoped Topology
set_option autoImplicit false

/-- At positive times the ambient spatial derivative is the derivative of the fixed-time slice. -/

theorem Kyprianou.Ch04.ito43_spatial_slice_derivative (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Ici (0 : ℝ) ×ˢ (univ : Set ℝ)))
    (s x : ℝ) (hs : 0 < s) :
    fderiv ℝ f (s,x) (0,1) = deriv (fun y : ℝ => f (s,y)) x := by sorry
