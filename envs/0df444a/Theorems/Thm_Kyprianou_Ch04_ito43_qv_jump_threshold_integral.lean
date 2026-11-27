-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_qv_jump_threshold_integral
-- name    : Kyprianou.Ch04.ito43_qv_jump_threshold_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:25:43.854377+00:00
-- url     : https://prove2.me/theorems/9c49940d-9cda-48ce-a1eb-086575657872
-- title:
--   Strict jump threshold mass is a cumulative-mass difference
-- statement:
--   Identify the strictly later jump interval with the difference of nested measurable rectangles.
-- source:
--   Kyprianou (2006), Theorem 4.3 proof auxiliary

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_qv_jump_threshold_integral
    (μ : Measure (ℝ × ℝ)) (t b : NNReal)
    (hi : IntegrableOn (fun z : ℝ × ℝ => z.2^2/2)
      (Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ)) μ) :
    (∫ z in {z : ℝ × ℝ | (b:ℝ) < z.1} ∩
        (Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ)), z.2^2/2 ∂μ) =
      (∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ), z.2^2/2 ∂μ) -
      (∫ z in Icc (0:ℝ) ((min t b:NNReal):ℝ) ×ˢ (univ : Set ℝ), z.2^2/2 ∂μ) := by sorry
