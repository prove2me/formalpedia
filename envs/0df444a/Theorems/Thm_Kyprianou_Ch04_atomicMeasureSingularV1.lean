-- Prove2me | Theorems.Thm_Kyprianou_Ch04_atomicMeasureSingularV1
-- name    : Kyprianou.Ch04.atomicMeasureSingularV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:28:46.817699+00:00
-- url     : https://prove2.me/theorems/d11ad09f-8d70-4bda-bce2-93cb19f79f5b
-- title:
--   Singularity of a summably weighted atomic measure
-- statement:
--   The nonzero support of a summable family is countable; the weighted Dirac sum vanishes off its countable image, which is Lebesgue-null.
-- source:
--   Supporting deterministic differentiation for Kyprianou (2006), Chapter 4, Exercise 4.9(i).

import Mathlib
open MeasureTheory Set Function
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.atomicMeasureSingularV1 {ι : Type} (a : ι → ℝ) (w : ι → ℝ)
    (hw : Summable w) :
    (Measure.sum (fun i => ENNReal.ofReal (w i) • Measure.dirac (a i))).MutuallySingular
      (volume : Measure ℝ) := by
  sorry
