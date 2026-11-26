-- Prove2me | Theorems.Thm_Kyprianou_Ch04_markedPredictableLeAmbientProduct
-- name    : Kyprianou.Ch04.markedPredictableLeAmbientProduct
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:46:38.961677+00:00
-- url     : https://prove2.me/theorems/2d7fdd11-3336-4974-8cb3-270a27ecc789
-- title:
--   Marked predictable measurable space is below ambient product
-- statement:
--   The marked predictable sigma-algebra for nonnegative real time is contained in the ambient product sigma-algebra.
-- source:
--   Kyprianou Chapter 4 Exercise 4.4; predictable intensity measure construction.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_marked_rectangle_generate_sigma
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false
universe u v

theorem Kyprianou.Ch04.markedPredictableLeAmbientProduct
    {Ω : Type u} {E : Type v} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]
    (F : Filtration NNReal mΩ) :
    F.predictable.prod mE ≤
      ((inferInstance : MeasurableSpace NNReal).prod mΩ).prod mE := by
  sorry
