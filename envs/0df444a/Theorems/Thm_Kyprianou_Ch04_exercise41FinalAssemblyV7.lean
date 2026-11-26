-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41FinalAssemblyV7
-- name    : Kyprianou.Ch04.exercise41FinalAssemblyV7
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:17:07.683584+00:00
-- url     : https://prove2.me/theorems/2e8a70f0-29e4-5340-ae8b-920b4ecd5941
-- title:
--   Assemble the three integrable ledgers into the exact discontinuous chain rule
-- statement:
--   Assemble the three integrable ledgers into the exact discontinuous chain rule
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41FinalAssemblyV7
    {Z : Type} [MeasurableSpace Z] (μ : Measure Z)
    (f fLeft fRight : ℝ → ℝ)
    (hLeft : ∀ x : ℝ, x < 0 → f x = fLeft x)
    (hRight : ∀ x : ℝ, 0 < x → f x = fRight x)
    (x0 xt D : ℝ) (pre post : Z → ℝ)
    (l : NNReal → ℝ) (t : NNReal) (S : Finset NNReal)
    (hC : let g := fun x : ℝ => if x < 0 then fLeft x - fLeft 0
          else if 0 < x then fRight x - fRight 0 else 0
      Integrable (fun z => g (post z) - g (pre z)) μ ∧
      g xt = g x0 + D + ∫ z, (g (post z) - g (pre z)) ∂μ)
    (hB : let a := fun x : ℝ => if 0 ≤ x then (1 : ℝ) else 0
      let b := fun x : ℝ => if 0 < x then (1 : ℝ) else 0
      Integrable (fun z => a (post z) - a (pre z)) μ ∧
      Integrable (fun z => b (post z) - b (pre z)) μ ∧
      a xt = a x0 + (∫ z, (a (post z) - a (pre z)) ∂μ) +
        (∑ s ∈ S, if l s = 0 then 1 else 0) ∧
      b xt = b x0 + (∫ z, (b (post z) - b (pre z)) ∂μ) +
        ((if 0 < t then 1 else 0) + ∑ s ∈ S, if s < t then 1 else 0)) :
    f xt = f x0 + D + (∫ z, (f (post z) - f (pre z)) ∂μ) +
      (if 0 < t then fRight 0 - f 0 else 0) +
      ∑ s ∈ S, ((if l s = 0 then f 0 - fLeft 0 else 0) +
        (if s < t then fRight 0 - f 0 else 0)) := by
  sorry
