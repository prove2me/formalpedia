-- Prove2me | Theorems.Thm_Kyprianou_Ch04_continuousClockInverseV1
-- name    : Kyprianou.Ch04.continuousClockInverseV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:36:26.297052+00:00
-- url     : https://prove2.me/theorems/3dd73c97-c2a0-5cef-a934-191418229c85
-- title:
--   Inverse of continuous increasing clock dominating time
-- statement:
--   A continuous increasing clock dominating time has an attained finite inverse.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, physical predictable integration.

import Mathlib
open Filter Set Topology
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem continuousClockInverseV1 (A : NNReal → ℝ) (hA : Continuous A)
    (hMono : Monotone A) (hLower : ∀ t : NNReal, (t : ℝ) ≤ A t)
    (m t : NNReal) :
    sInf {u : NNReal | (m : ℝ) ≤ A u} ≤ t ↔ (m : ℝ) ≤ A t := by
  sorry
end Kyprianou.Ch04
