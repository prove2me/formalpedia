-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_zero_near_origin
-- name    : Kyprianou.Ch04.ito43_cutoff_zero_near_origin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:43:24.623855+00:00
-- url     : https://prove2.me/theorems/1e186c2f-90a3-40b5-8242-8f298c6c521f
-- title:
--   Continuous cutoff vanishes near zero
-- statement:
--   The cutoff is continuous, takes values between zero and one and vanishes on the closed interval of radius one over the cutoff index plus one.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_cutoff_zero_near_origin (m : ℕ) :
    let chi : ℝ → ℝ := fun z => min 1 (max 0 (|z| * ((m:ℝ)+1)-1))
    Continuous chi ∧ (∀ z, 0 ≤ chi z ∧ chi z ≤ 1) ∧
      (∀ z, |z| * ((m:ℝ)+1) ≤ 1 → chi z = 0) := by sorry
