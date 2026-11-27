-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteMartingaleAbsSupSubmartingaleV1
-- name    : Kyprianou.Ch04.finiteMartingaleAbsSupSubmartingaleV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-27T00:34:43.719496+00:00
-- url     : https://prove2.me/theorems/3e1a6475-ab9b-54e8-8fc5-e2d4dd089463
-- title:
--   finiteMartingaleAbsSupSubmartingaleV1
-- statement:
--   Finite martingale maximum inequality for rectangular cutoff-time grids.
-- source:
--   Kyprianou (2006), Exercise 4.5, small-jump cutoff limit

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The maximum of the absolute values of finitely many real martingales
is a nonnegative submartingale. -/

theorem Kyprianou.Ch04.finiteMartingaleAbsSupSubmartingaleV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F : Filtration ℕ inferInstance)
    (M : ℕ → ℕ → Ω → ℝ) (n : ℕ) (hM : ∀ j ≤ n, Martingale (M j) F P) :
    Submartingale (fun i w => (Finset.range (n+1)).sup'
      Finset.nonempty_range_add_one (fun j => |M j i w|)) F P := by
  sorry
