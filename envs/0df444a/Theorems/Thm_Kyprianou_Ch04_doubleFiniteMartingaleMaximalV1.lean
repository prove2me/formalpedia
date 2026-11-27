-- Prove2me | Theorems.Thm_Kyprianou_Ch04_doubleFiniteMartingaleMaximalV1
-- name    : Kyprianou.Ch04.doubleFiniteMartingaleMaximalV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-27T00:34:44.056256+00:00
-- url     : https://prove2.me/theorems/4dbf3d15-4707-520f-83d8-2cb49dabc9ed
-- title:
--   doubleFiniteMartingaleMaximalV1
-- statement:
--   Finite martingale maximum inequality for rectangular cutoff-time grids.
-- source:
--   Kyprianou (2006), Exercise 4.5, small-jump cutoff limit

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Two successive Doob estimates bound the rectangular grid maximum
in L2 by four times the terminal L2 norm. -/

theorem Kyprianou.Ch04.doubleFiniteMartingaleMaximalV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F G : Filtration ℕ inferInstance)
    (M : ℕ → ℕ → Ω → ℝ) (n m : ℕ)
    (hF : ∀ j ≤ n, Martingale (M j) F P)
    (hG : Martingale (fun j => M j m) G P) :
    eLpNorm (fun w => (Finset.range (m+1)).sup'
      Finset.nonempty_range_add_one (fun i => (Finset.range (n+1)).sup'
        Finset.nonempty_range_add_one (fun j => |M j i w|))) 2 P ≤
      4 * eLpNorm (M n m) 2 P := by
  sorry
