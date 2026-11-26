-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46RestrictedFutureProductLawV1
-- name    : Kyprianou.Ch04.exercise46RestrictedFutureProductLawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:33:29.416942+00:00
-- url     : https://prove2.me/theorems/a6eb72e1-e7f9-58bb-bb3d-0af5b9ba1768
-- title:
--   Product law from stopped-event restricted future laws
-- statement:
--   Check measurable rectangles using the restricted law, then use uniqueness of finite product measures.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46RestrictedFutureProductLawV1
    {Omega E H : Type} [MeasurableSpace Omega] [MeasurableSpace E] [MeasurableSpace H]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (J : Omega → H) (Z Y : Omega → E)
    (hJ : Measurable J) (hZ : AEMeasurable Z P) (hY : Measurable Y)
    (hLaw : ∀ S : Set H, MeasurableSet S →
      (P.restrict (J ⁻¹' S)).map Z = P (J ⁻¹' S) • P.map Y) :
    P.map (fun w => (J w,Z w)) = (P.map J).prod (P.map Y) := by
  sorry
