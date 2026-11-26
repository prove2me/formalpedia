-- Prove2me | Theorems.Thm_Kyprianou_Ch04_boundedPredictableMarkMaskV1
-- name    : Kyprianou.Ch04.boundedPredictableMarkMaskV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:30:23.061799+00:00
-- url     : https://prove2.me/theorems/4f742b67-347f-547b-999e-55245e49e247
-- title:
--   Bounded measurable predictable marked mask
-- statement:
--   Mark-masked predictable weights with bounded marks are measurable,
--   bounded and supported on the chosen finite mark band.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem boundedPredictableMarkMaskV1 {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration NNReal inferInstance)
    (B : Set ℝ) (hB : MeasurableSet B) (hmark : ∀ z ∈ B, |z| ≤ 1)
    (W : NNReal × Ω → ℝ) (hW : Measurable[F.predictable] W)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ p, |W p| ≤ K) :
    let g := fun p : (NNReal × Ω) × ℝ =>
      B.indicator (fun z => z * W p.1) p.2
    Measurable[F.predictable.prod inferInstance] g ∧
      (∀ p, ‖g p‖ ≤ K) ∧ (∀ p, p.2 ∉ B → g p = 0) := by
  sorry
end Kyprianou.Ch04
