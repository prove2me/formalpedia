-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_jump_kernel_finite_abs_sum_bound
-- name    : Kyprianou.Ch04.ito43_jump_kernel_finite_abs_sum_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:31:28.407912+00:00
-- url     : https://prove2.me/theorems/930ea10a-3b0a-4adb-a455-d0f5b8102320
-- title:
--   Finite absolute jump-kernel sums bounded by total squared jump energy
-- statement:
--   Finite absolute jump-kernel sums bounded by total squared jump energy.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

theorem Kyprianou.Ch04.ito43_jump_kernel_finite_abs_sum_bound {Ω : Type} [MeasurableSpace Ω]
    (X L : NNReal → Ω → ℝ) (w : Ω)
    (hJ : ({s : NNReal | 0 < s ∧ X s w ≠ L s w}).Countable)
    (T t : NNReal) (ht : t ≤ T) (C : ℝ) (hC : 0 ≤ C)
    (hE : Summable (fun s : Ioc (0 : NNReal) T => (X s w-L s w)^2))
    (F : ℝ × ℝ → ℝ)
    (hb : ∀ s : NNReal, 0 < s → s ≤ t →
      |F ((s : ℝ), X s w-L s w)| ≤ C*(X s w-L s w)^2) :
    let B : Set (ℝ × ℝ) := Icc (0 : ℝ) (t : ℝ) ×ˢ univ
    let J : Set NNReal := {s | 0 < s ∧ X s w ≠ L s w}
    let φ : J → ℝ × ℝ := fun s => (((s : NNReal) : ℝ), X s w-L s w)
    ∀ S : Finset J, (∑ s ∈ S, |B.indicator F (φ s)|) ≤
      C * ∑' s : Ioc (0 : NNReal) T, (X s w-L s w)^2 := by sorry
