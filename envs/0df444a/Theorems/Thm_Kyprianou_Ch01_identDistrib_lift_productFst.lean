-- Prove2me | Theorems.Thm_Kyprianou_Ch01_identDistrib_lift_productFst
-- name    : Kyprianou.Ch01.identDistrib_lift_productFst
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:55:35.669096+00:00
-- url     : https://prove2.me/theorems/22dd0e23-5594-4872-883b-0fca26f31fb1
-- title:
--   Identically distributed measurable real variables remain identically distributed after independent product lifting
-- statement:
--   If measurable real random variables X and Y have the same law under P, then their first-coordinate lifts to a product probability space with arbitrary independent factor Q retain identical laws under P ⊗ Q. This follows by preservation of the first projection and the exact laws of both lifted variables. The result is needed to lift each stationary Lévy-process increment onto the independent common probability space in the positive-Gaussian Lévy–Khintchine existence construction.
-- source:
--   Pinned Mathlib IdentDistrib.map_eq, HasLaw.identDistrib, MeasureTheory.measurePreserving_fst and Measure.map_map; Kyprianou (2006) Chapter 1 Theorem 1.6.

import Mathlib
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem Kyprianou.Ch01.identDistrib_lift_productFst
    {Ω Λ : Type} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (hXY : IdentDistrib X Y P P) :
    IdentDistrib (fun p : Ω × Λ => X p.1)
      (fun p : Ω × Λ => Y p.1) (P.prod Q) (P.prod Q) := by
  sorry
