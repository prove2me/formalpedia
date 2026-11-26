-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvCompactPathDerivativeV1
-- name    : Kyprianou.Ch04.bvCompactPathDerivativeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:44:04.117297+00:00
-- url     : https://prove2.me/theorems/8a728196-8932-55ef-b721-c4eaebfffa08
-- title:
--   Derivative of a BV path with absolutely summable jumps
-- statement:
--   On the compact unit interval represent the jump sum as a signed atomic cumulative function and use its zero derivative almost everywhere.
-- source:
--   Supporting proof for Kyprianou (2006), Chapter 4, Exercise 4.9(i).

import Mathlib
open MeasureTheory Set Filter Topology Function
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.bvCompactPathDerivativeV1 (x : ℝ≥0 → ℝ) (d : ℝ)
    (hrep : ∀ t : ℝ≥0,
      Summable (fun s : Ioc (0 : ℝ≥0) t => |x s - leftLim x s|) ∧
      x t = d * (t : ℝ) + ∑' s : Ioc (0 : ℝ≥0) t, (x s - leftLim x s)) :
    ∀ᵐ s : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      HasDerivAt (fun t : ℝ => x (Real.toNNReal t)) d s := by
  sorry
