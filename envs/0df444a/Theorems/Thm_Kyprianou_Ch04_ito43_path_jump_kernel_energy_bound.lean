-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_path_jump_kernel_energy_bound
-- name    : Kyprianou.Ch04.ito43_path_jump_kernel_energy_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:27:18.417497+00:00
-- url     : https://prove2.me/theorems/31023e45-a8d2-4610-8fe4-f6f87c8d7429
-- title:
--   Quadratic energy dominates integrable actual jump kernels
-- statement:
--   Quadratic energy dominates integrable actual jump kernels.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

/-- Any jump kernel dominated by squared jump energy on a compact horizon is integrable,
and its integral is bounded by that energy. -/

theorem Kyprianou.Ch04.ito43_path_jump_kernel_energy_bound {Ω : Type} [MeasurableSpace Ω]
    (X L : NNReal → Ω → ℝ) (w : Ω)
    (hJ : ({s : NNReal | 0 < s ∧ X s w ≠ L s w}).Countable)
    (T t : NNReal) (ht : t ≤ T) (C : ℝ) (hC : 0 ≤ C)
    (hE : Summable (fun s : Ioc (0 : NNReal) T => (X s w-L s w)^2))
    (F : ℝ × ℝ → ℝ)
    (hb : ∀ s : NNReal, 0 < s → s ≤ t →
      |F ((s : ℝ), X s w-L s w)| ≤ C*(X s w-L s w)^2) :
    let B : Set (ℝ × ℝ) := Icc (0 : ℝ) (t : ℝ) ×ˢ univ
    IntegrableOn F B (pathJumpMeasure X L w) ∧
      |∫ z in B, F z ∂(pathJumpMeasure X L w)| ≤
        C * ∑' s : Ioc (0 : NNReal) T, (X s w-L s w)^2 := by sorry
