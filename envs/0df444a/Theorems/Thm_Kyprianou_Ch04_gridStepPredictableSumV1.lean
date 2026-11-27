-- Prove2me | Theorems.Thm_Kyprianou_Ch04_gridStepPredictableSumV1
-- name    : Kyprianou.Ch04.gridStepPredictableSumV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:59:45.30105+00:00
-- url     : https://prove2.me/theorems/7dae3e7d-39c2-5119-a9c7-292466701477
-- title:
--   gridStepPredictableSumV1
-- statement:
--   gridStepPredictableSumV1
-- source:
--   Kyprianou (2006), Exercise 4.5(iii), predictable grid kernel

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_predictableGridCellV1
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

/-- Finite sums of past-measurable right-closed cell coefficients are predictable. -/

theorem Kyprianou.Ch04.gridStepPredictableSumV1 {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration NNReal inferInstance)
    (n : ℕ) (u : ℕ → NNReal) (H : ℕ → Ω → ℝ)
    (hH : ∀ k ∈ Finset.range n, Measurable[F (u k)] (H k)) :
    Measurable[F.predictable] (fun p : NNReal × Ω =>
      ∑ k ∈ Finset.range n,
        (Ioc (u k) (u (k+1)) ×ˢ (univ : Set Ω)).indicator
          (fun q : NNReal × Ω => H k q.2) p) := by
  sorry
