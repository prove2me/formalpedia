-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45RectangularMaxSubmartingaleV1
-- name    : Kyprianou.Ch04.exercise45RectangularMaxSubmartingaleV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-27T00:42:59.53352+00:00
-- url     : https://prove2.me/theorems/da959051-e224-4ba6-84a9-6698adfda5d8
-- title:
--   Finite absolute martingale maximum is a submartingale
-- statement:
--   Use the maximum of a martingale and its negative to obtain the absolute-value submartingale; induct over the finite maximum using the supremum of two submartingales.
-- source:
--   Kyprianou (2006), Exercise 4.5 proof auxiliary

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45RectangularMaxSubmartingaleV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (S : ℕ → ℕ → Ω → ℝ)
    (h : ∀ j : ℕ, Martingale (fun i w => S i j w) F P)
    (m : ℕ) :
    Submartingale
      (fun i w => (Finset.range (m+1)).sup' Finset.nonempty_range_add_one
        (fun j => |S i j w|)) F P := by sorry
