-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41LedgerCombineV2
-- name    : Kyprianou.Ch04.exercise41LedgerCombineV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:31:58.677206+00:00
-- url     : https://prove2.me/theorems/55424245-7a34-46a9-add7-2ab60049cd45
-- title:
--   Combine continuous and two indicator jump ledgers
-- statement:
--   Combine continuous and two indicator jump ledgers
-- source:
--   Kyprianou (2006), Chapter 4, Exercises 4.1 and 4.9.

import Mathlib
open MeasureTheory
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41LedgerCombineV2
    {Z : Type} [MeasurableSpace Z]
    (μ : Measure Z)
    (f g a b : ℝ → ℝ)
    (c α β x0 xt D A B : ℝ)
    (pre post : Z → ℝ)
    (hSplit : ∀ x, f x = g x + c + α * a x + β * b x)
    (hg : Integrable (fun z => g (post z) - g (pre z)) μ)
    (ha : Integrable (fun z => a (post z) - a (pre z)) μ)
    (hb : Integrable (fun z => b (post z) - b (pre z)) μ)
    (hG : g xt = g x0 + D + ∫ z, (g (post z) - g (pre z)) ∂μ)
    (hA : a xt = a x0 + (∫ z, (a (post z) - a (pre z)) ∂μ) + A)
    (hB : b xt = b x0 + (∫ z, (b (post z) - b (pre z)) ∂μ) + B) :
    f xt = f x0 + D + (∫ z, (f (post z) - f (pre z)) ∂μ) +
      α * A + β * B  := by
  sorry
