-- Prove2me | Theorems.Thm_Kyprianou_Ch04_predictableGridCellV1
-- name    : Kyprianou.Ch04.predictableGridCellV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:55:13.873847+00:00
-- url     : https://prove2.me/theorems/f819db6b-988b-4a0c-9e55-8ccf66209847
-- title:
--   predictableGridCellV1
-- statement:
--   predictableGridCellV1
-- source:
--   Kyprianou (2006), Exercise 4.5(iii), physical clipped-grid uniform cutoff estimate

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.predictableGridCellV1
    {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration NNReal inferInstance) (a b : NNReal) (H : Ω → ℝ)
    (hH : Measurable[F a] H) :
    Measurable[F.predictable] ((Ioc a b ×ˢ (univ : Set Ω)).indicator
      (fun p : NNReal × Ω => H p.2)) := by
  sorry
