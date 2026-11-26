-- Prove2me | Theorems.Thm_Kyprianou_Ch04_expandingGeometricUniformCauchyV1
-- name    : Kyprianou.Ch04.expandingGeometricUniformCauchyV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:07:59.70692+00:00
-- url     : https://prove2.me/theorems/7124df3e-2e3d-57f1-bfd9-7e1bc88f6d6c
-- title:
--   Expanding-horizon geometric increments give local uniform Cauchy convergence
-- statement:
--   Expanding-horizon geometric increments give local uniform Cauchy convergence.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii).

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology UniformConvergence
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem expandingGeometricUniformCauchyV1 {E : Type} [MetricSpace E] [CompleteSpace E]
    (Y : ℕ → NNReal → E)
    (h : ∀ᶠ n : ℕ in atTop, ∀ t ≤ (n : NNReal),
      dist (Y n t) (Y (n+1) t) ≤ (2⁻¹ : ℝ)^n) :
    ∀ T : NNReal, UniformCauchySeqOn Y atTop (Icc 0 T) := by
  sorry
end Kyprianou.Ch04
