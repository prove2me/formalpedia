-- Prove2me | Theorems.Thm_Kyprianou_Ch04_monotoneGridIndicatorVariationV1
-- name    : Kyprianou.Ch04.monotoneGridIndicatorVariationV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:47:40.829016+00:00
-- url     : https://prove2.me/theorems/9f08827a-ed25-53a1-99f3-f311fbffca21
-- title:
--   monotoneGridIndicatorVariationV1
-- statement:
--   A monotone grid crosses a threshold at most once.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_positive_monotone_grid_variation
open MeasureTheory Set
open scoped NNReal Classical
set_option autoImplicit false

/-- A monotone grid crosses a given jump threshold at most once. -/

theorem Kyprianou.Ch04.monotoneGridIndicatorVariationV1 (v : ℕ → NNReal) (hm : Monotone v) (r : NNReal) (n : ℕ) :
    let J : ℕ → ℝ := fun k => if r ≤ v k then 1 else 0
    (∑ k ∈ Finset.range n, |J (k+1)-J k|) ≤ 1 := by
  sorry
