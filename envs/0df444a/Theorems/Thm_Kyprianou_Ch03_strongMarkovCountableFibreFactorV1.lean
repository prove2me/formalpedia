-- Prove2me | Theorems.Thm_Kyprianou_Ch03_strongMarkovCountableFibreFactorV1
-- name    : Kyprianou.Ch03.strongMarkovCountableFibreFactorV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:06:01.818672+00:00
-- url     : https://prove2.me/theorems/88957651-8d19-496a-b63e-adb9859cacd6
-- title:
--   Restricted countable-fibre measure factor
-- statement:
--   Disintegrate the restricted measure into its countably many disjoint fibres, use map congruence on each fibre, and sum the scalar factors.
-- source:
--   Kyprianou (2006), Theorem 3.1; countable-grid restricted law ce10a41b-6699-4acd-b73c-5cedfb05d77b.

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.strongMarkovCountableFibreFactorV1
    {Omega I E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (D : Set Omega) (hD : MeasurableSet D)
    (T : Omega → I) (hCount : Countable (Set.range T))
    (Y : I → Omega → E) (Z : Omega → E) (nu : Measure E)
    (hZ : Measurable Z)
    (hEq : ∀ w, Z w = Y (T w) w)
    (hFib : ∀ i : I, MeasurableSet (D ∩ {w | T w = i}))
    (hLaw : ∀ i : I, Measure.map (Y i) (P.restrict (D ∩ {w | T w = i})) =
      P (D ∩ {w | T w = i}) • nu) :
    Measure.map Z (P.restrict D) = P D • nu := by
  sorry
