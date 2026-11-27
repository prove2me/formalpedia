-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45RectangularDoobV1
-- name    : Kyprianou.Ch04.exercise45RectangularDoobV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-27T00:42:57.289047+00:00
-- url     : https://prove2.me/theorems/6fd3c5b7-267d-48a6-bb75-cf851a0f2f93
-- title:
--   Two successive Doob inequalities bound the rectangular maximum
-- statement:
--   Use Doob in time on the submartingale formed by the maximum across cutoff indices, then use Doob in cutoff index at the terminal time.
-- source:
--   Kyprianou (2006), Exercise 4.5 proof auxiliary

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45RectangularDoobV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F G : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (S : ℕ → ℕ → Ω → ℝ)
    (hF : ∀ j : ℕ, Martingale (fun i w => S i j w) F P)
    (hG : ∀ i : ℕ, Martingale (fun j w => S i j w) G P)
    (n m : ℕ) :
    eLpNorm (fun w => (Finset.range (n+1)).sup' Finset.nonempty_range_add_one
      (fun i => (Finset.range (m+1)).sup' Finset.nonempty_range_add_one
        (fun j => |S i j w|))) 2 P ≤
      4 * eLpNorm (S n m) 2 P := by sorry
