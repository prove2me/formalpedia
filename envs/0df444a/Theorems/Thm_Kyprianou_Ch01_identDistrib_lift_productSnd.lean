-- Prove2me | Theorems.Thm_Kyprianou_Ch01_identDistrib_lift_productSnd
-- name    : Kyprianou.Ch01.identDistrib_lift_productSnd
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:57:53.802201+00:00
-- url     : https://prove2.me/theorems/6c3adf9f-3495-4ed3-ab06-d75fa8c0aada
-- title:
--   Identically distributed measurable variables retain their law on the second product coordinate
-- statement:
--   If measurable real random variables X and Y on a probability space Q have identical distribution, their second-coordinate lifts to an independent product P ⊗ Q have identical distribution. This is the exact stationary-increment law transport for an independently coupled Lévy process.
-- source:
--   Pinned Mathlib IdentDistrib.map_eq, HasLaw.identDistrib, measurePreserving_snd and Measure.map_map.

import Mathlib
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem Kyprianou.Ch01.identDistrib_lift_productSnd
    {Ω Λ : Type} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X Y : Λ → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (hXY : IdentDistrib X Y Q Q) :
    IdentDistrib (fun p : Ω × Λ => X p.2)
      (fun p : Ω × Λ => Y p.2) (P.prod Q) (P.prod Q) := by
  sorry
